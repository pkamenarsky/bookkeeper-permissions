{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Bookkeeper.Permissions
  (
-- * Introduction
--
-- | This experimental library adds permissions to
-- <https://hackage.haskell.org/package/bookkeeper bookkeeper> records. Its
-- intended purpose is to be used as a building block in other libraries
-- providing general access to data in some form or other (database bindings,
-- web servers etc).
--
-- A common pattern in user facing programs is the following:
--
-- > doAdminStuff admin = do
-- >   when admin $ do
-- >    ...
--
-- But this is not enforced by the type system and can thus easily be forgotten
-- or gotten wrong. The approach that this library takes to getting the type
-- system work for us is to protect /data/ by requiring that record fields are
-- marked with specific /permissions/ that need to be provided when accessing
-- said fields.
--
-- This library uses <https://hackage.haskell.org/package/bookkeeper bookkeeper>
-- for the sake of simplicity, but porting it to another record library like
-- <http://hackage.haskell.org/package/rawr rawr> shouldn't be too much work.
-- The aim is to see if the approach taken is generally useful and generalizes
-- well.
--
-- Let's start by defining some custom permissions:
--
-- > data Admin = Admin
-- > data Auth  = Auth
--
-- And a record with protected fields:
--
-- > type Person = Book
-- >  '[ "name" :=> Permission
-- >       '[ "modify" :=> (Admin :&: Auth)
-- >        , "insert" :=> Auth
-- >        ] String
-- >   , "age"  :=> Permission
-- >       '[ "modify" :=> Auth
-- >        , "insert" :=> Auth
-- >        ] Int
-- >  ]
--
-- /Note:/ 'unsafePermission' shouldn't be called from user code. It is intended
-- to be called by other libraries only (i.e. database access layer). It's
-- only used here to easily create a value with protected fields.
--
-- > person :: Person
-- > person = emptyBook
-- >   & #name =: unsafePermission "person"
-- >   & #age  =: unsafePermission 6
--
-- This is a normal 'Book', except that its fields are protected by the
-- opaque data type 'Permission'. A 'Permission' takes the following form:
--
-- > Permission [ mode :=> permissions, mode2 :=> permissions2 ] type
--
-- /Modes/ help define permissions for different purposes, i.e. reading or
-- modifying. Modes can be arbitrary, but certain functions like 'modify' or
-- 'insert' expect certain modes to be present.
--
-- Different permissions can be mixed with the ':|:' (/boolean or/) and ':&:'
-- (/boolean and/) operators, i.e:
--
-- > Permission [ "modify" :=> (Admin :&: Auth)] String
--
-- This means that the field can be accessed only when /both/ permissions
-- 'Admin' and 'Auth' are provided. Contrast this with:
--
-- > Permission [ "modify" :=> (Admin :|: Auth)] String
--
-- which means that access is granted by providing at least one of the
-- required permissions.
--
-- ':|:' and ':&:' can be nested arbitrarily.
--
-- Now, the general idea is to provide a list of permissions when
-- accessing protected data:
--
-- > modify (Auth `Set.Ext` Set.Empty) f person
-- >   where f = ...
--
-- The provided list of permissions is used to /eliminate/ the 'Permission'
-- constructor from all fields that require less or equal permissions to those
-- provided in the permissions list. The above would eliminate the 'Permission'
-- constructor from the field "age", but would leave the type of "name" as:
--
-- > Permission [ "modify" :=> Admin ] String
--
-- meaning that it can't be accessed without providing the permission 'Admin'.
-- The whole type of 'f' would be:
--
-- > f :: Book' '[ "age" :=> Int
-- >             , "name" :=> Permission '["modify" :=> Admin] String
-- >             ]
-- >   -> Book' '[ "age" :=> Int
-- >             , "name" :=> Permission '["modify" :=> Admin] String
-- >             ]
--
-- In constrast, the following:
--
-- > modify (Admin `Set.Ext` (Auth `Set.Ext` Set.Empty)) f person
-- >   where f = ...
--
-- would provide access to all fields.

-- * Permissions
    Permission
  , (:|:), (:&:)

-- * Reading
  , Bookkeeper.Permissions.read

-- * Modification
  , modify

-- * Insertion
  , insert

-- * Unsafe
  , unsafePermission
  , unsafeUnpackPermission

-- * Type families & classes
  , ElimListM
  , ElimList

  , mapADT
  ) where

import Prelude hiding (and)

import Data.Typeable

import GHC.TypeLits
import GHC.OverloadedLabels
import GHC.Generics hiding (C, D)

import Data.Proxy

import Bookkeeper hiding (modify)
import Bookkeeper.Internal hiding (modify)

import qualified Data.Type.Map as Map
import qualified Data.Type.Set as Set

import Unsafe.Coerce

--------------------------------------------------------------------------------

type Iso a b = (a -> b, b -> a)

iso :: (a -> b) -> (b -> a) -> Iso a b
iso = (,)

data Star

-- | Type level boolean /or/.
data a :|: b

-- | Type level boolean /and/.
data a :&: b

-- | An opaque data type used for protecting record fields.
data Permission pr a = Permission a deriving (Eq, Generic, Typeable, Show)

cnvPermission :: Permission prf a -> Permission prf' a
cnvPermission (Permission a) = Permission a

-- | Used to create protected values. Shouldn't be called from user code.
unsafePermission :: a -> Permission prf a
unsafePermission = Permission

-- | Used to unpack protected values. Shouldn't be called from user code.
unsafeUnpackPermission :: Permission prf a -> a
unsafeUnpackPermission (Permission a) = a

type family ElimTerm1M prf x where
  ElimTerm1M prf (op () x)    = ElimTerm1M prf x
  ElimTerm1M prf (op x ())    = ElimTerm1M prf x
  ElimTerm1M prf (prf :&: x)  = ElimTerm1M prf x
  ElimTerm1M prf (x :&: prf)  = ElimTerm1M prf x
  ElimTerm1M prf (op prf prf) = ()
  ElimTerm1M prf (prf :|: x)  = ()
  ElimTerm1M prf (x :|: prf)  = ()
  ElimTerm1M prf prf          = ()
  ElimTerm1M prf x            = x

data ModeNotFound

type family ElimTermM prf x where
  ElimTermM Star x               = ()
  ElimTermM prf ('Just prf)      = ()
  ElimTermM prf ('Just x)        = ElimTerm1M prf x
  ElimTermM prf ('Just (op x y)) = ElimTerm1M prf (op (ElimTermM prf  ('Just x)) (ElimTermM prf  ('Just y)))
  ElimTermM prf 'Nothing         = ModeNotFound

--------------------------------------------------------------------------------

type family UnpackPermissionM mode prf a where
  UnpackPermissionM mode prf (Permission '[mode :=> ()] a)           = ElimM mode prf a
  UnpackPermissionM mode prf (Permission '[mode :=> ModeNotFound] a) = TypeError ('Text "Mode " ':<>: 'ShowType mode ':<>: 'Text " isn't defined for all fields")
  UnpackPermissionM mode prf (Permission prf' a)                     = Permission prf' a

class UnpackPermission mode prf a where
  unpackPermission :: Proxy mode -> Proxy prf -> Iso a (UnpackPermissionM mode prf a)

instance ( Elim mode prf a
         , UnpackPermissionM mode prf (Permission '[mode :=> ()] a) ~ (ElimM mode prf a)
         ) => UnpackPermission mode prf (Permission '[mode :=> ()] a) where
  unpackPermission mode prf = iso (\(Permission a) -> fst (elim mode prf) a) (\a -> Permission (snd (elim mode prf) a))

instance {-# OVERLAPPABLE #-} (UnpackPermissionM mode prf (Permission prf' a) ~ Permission prf' a) => UnpackPermission mode prf (Permission prf' a) where
  unpackPermission _ _ = iso id id

type family ElimM mode prf a where
  ElimM mode prf (Book' kvs) = Book' (ElimBookM mode prf kvs)
  ElimM mode prf x           = x

class Elim mode prf a where
  elim :: Proxy mode -> Proxy prf -> Iso a (ElimM mode prf a)

instance (ElimBook mode prf kvs) => Elim mode prf (Book' kvs) where
  elim mode prf = iso (\a -> (fst (elimBook mode prf) a)) (\a -> (snd (elimBook mode prf) a))

instance {-# OVERLAPPABLE #-} (ElimM mode prf a ~ a) => Elim mode prf a where
  elim _ _ = iso id id

type family ElimBookM mode prf a where
  ElimBookM mode prf '[] = '[]
  ElimBookM mode prf ((k :=> Permission prf' v) ': m) = (k :=> UnpackPermissionM mode prf (Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v)) ': ElimBookM mode prf m
  ElimBookM mode prf ((k :=> v) ': m) = (k :=> ElimM mode prf v) ': ElimBookM mode prf m

class ElimBook mode prf a where
  elimBook :: Proxy mode -> Proxy prf -> Iso (Book' a) (Book' (ElimBookM mode prf a))

instance (ElimBookM mode prf '[] ~ '[]) => ElimBook mode prf '[] where
  elimBook _ _ = iso id id

instance {-# OVERLAPPABLE #-}
    ( UnpackPermission mode prf (Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v)
    , ElimBook mode prf m
    ) => ElimBook mode prf ((k :=> Permission prf' v) ': m) where
  elimBook mode prf = iso
    (\(Book (Map.Ext k v m)) -> Book (Map.Ext k (fst (unpackPermission mode prf) (cnvPermission v :: (Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v))) (getBook (fst (elimBook mode prf) (Book m)))))
    (\(Book (Map.Ext k v m)) -> Book (Map.Ext k (cnvPermission (snd (unpackPermission mode prf) v :: Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v)) (getBook (snd (elimBook mode prf) (Book m)))))

instance {-# OVERLAPPABLE #-}
    ( Elim mode prf v
    , ElimBook mode prf m
    , ElimBookM mode prf ((k :=> v) ': m) ~ ((k :=> ElimM mode prf v) ': ElimBookM mode prf m)
    ) => ElimBook mode prf ((k :=> v) ': m) where
  elimBook mode prf = iso
    (\(Book (Map.Ext k v m)) -> (Book (Map.Ext k (fst (elim mode prf) v) (getBook (fst (elim mode prf) (Book m))))))
    (\(Book (Map.Ext k v m)) -> (Book (Map.Ext k (snd (elim mode prf) v) (getBook (snd (elim mode prf) (Book m))))))

type family ElimListM mode lst a where
  ElimListM mode '[] a    = a
  ElimListM mode (x:xs) a = ElimListM mode xs (ElimM mode x a)

class ElimList mode t a where
  elimList :: Proxy mode -> Set.Set t -> Iso a (ElimListM mode t a)

instance ElimList mode '[] a where
  elimList _ _ = iso id id

instance (Elim mode x a, ElimList mode xs (ElimM mode x a)) => ElimList mode (x : xs) a where
  elimList mode (Set.Ext _ xs) = iso
    ((fst (elimList mode xs)) . (fst (elim mode (Proxy :: Proxy x))))
    ((snd (elim mode (Proxy :: Proxy x))) . (snd (elimList mode xs)))

-- ADTs ------------------------------------------------------------------------

type family Merge a b where
  Merge (Book' xs) (Book' ys) = Book' (xs Set.:++ ys)
  Merge (Book' xs) () = Book' xs
  Merge x y = (x, y)

class ({- Rep b ~ a, -} UnRep a ~ b, Generic b) => UnGeneric a b | a -> b where
  type UnRep a

instance Generic (Book' '[]) where
  type Rep (Book' '[]) = U1
  from _ = U1
  to _   = Book (Map.Empty)

instance UnGeneric U1 (Book' '[]) where
  type UnRep U1 = Book' '[]

instance (Generic (Book' m)) => Generic (Book' (k :=> v ': m)) where
  type Rep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: Rep (Book' m)
  from (Book (Map.Ext k v m)) = M1 (K1 v) :*: from (Book m)
  to (M1 (K1 v) :*: m) = Book (Map.Ext (Map.Var :: Map.Var k) v (getBook (to m)))

instance ((Book' '[ k :=> d] `Merge` UnRep rest) ~ inst, Generic inst) => UnGeneric ((S1 (MetaSel (Just k) x y z) (K1 i d)) :*: rest) inst where
  type UnRep ((S1 (MetaSel (Just k) x y z) (K1 i d)) :*: rest) = Book' '[ k :=> d] `Merge` UnRep rest

type family MapGenericM mode prf a where
  MapGenericM mode prf (M1 i c f) = M1 i c (MapGenericM mode prf f)
  MapGenericM mode prf (K1 i (Permission prf c))   = K1 i c
  MapGenericM mode prf (K1 i c)   = K1 i c
  MapGenericM mode prf (f :*: g)  = MapGenericM mode prf f :*: MapGenericM mode prf g
  MapGenericM mode prf (f :+: g)  = MapGenericM mode prf f :+: MapGenericM mode prf g
  MapGenericM mode prf U1         = U1

class MapGeneric mode prf f where
  mapGeneric :: Proxy mode -> Set.Set prf -> f x -> MapGenericM mode prf f x

instance (MapGeneric mode prf f) => MapGeneric mode prf (M1 i c f) where
  mapGeneric mode prf (M1 c) = M1 (mapGeneric mode prf c)

instance MapGeneric mode prf (K1 i (Permission prf c)) where
  mapGeneric mode prf (K1 (Permission c)) = K1 c

instance (MapGenericM mode prf (K1 i c) ~ (K1 i c)) => MapGeneric mode prf (K1 i c) where
  mapGeneric mode prf (K1 c) = K1 c

instance (MapGeneric mode prf f, MapGeneric mode prf g) => MapGeneric mode prf (f :*: g) where
  mapGeneric mode prf (f :*: g) = mapGeneric mode prf f :*: mapGeneric mode prf g

instance (MapGeneric mode prf f, MapGeneric mode prf g) => MapGeneric mode prf (f :+: g) where
  mapGeneric mode prf (L1 f) = L1 (mapGeneric mode prf f)
  mapGeneric mode prf (R1 g) = R1 (mapGeneric mode prf g)

instance MapGeneric mode prf U1 where
  mapGeneric mode prf U1 = U1

type family MapADTM mode prf a where
  MapADTM mode prf (a b c d e) = (a (MapADTM mode prf b) (MapADTM mode prf c) (MapADTM mode prf d) (MapADTM mode prf e))
  MapADTM mode prf (a b c d) = (a (MapADTM mode prf b) (MapADTM mode prf c) (MapADTM mode prf d))
  MapADTM mode prf (a b c) = (a (MapADTM mode prf b) (MapADTM mode prf c))
  MapADTM mode prf (a b) = (a (MapADTM mode prf b))
  -- MapADTM mode prf a = ElimListM mode prf a
  MapADTM mode prf a = UnRep (MapGenericM mode prf (Rep a))

class MapADT mode prf f where
  mapADT :: Proxy mode -> Set.Set prf -> f -> MapADTM mode prf f
  default mapADT :: (Generic a, Generic (MapADTM mode prf a), GMapADT mode prf (Rep a) (Rep (MapADTM mode prf a))) => Proxy mode -> Set.Set prf -> a -> MapADTM mode prf a
  mapADT mode prf = to . gMapADT mode prf . from

instance ( Generic a
         , Generic (MapADTM mode prf a)
         , MapGenericM mode prf (Rep a) ~ (Rep (MapADTM mode prf a))
         , MapGeneric mode prf (Rep a)
         ) => MapADT mode prf a where
  mapADT mode prf = to . mapGeneric mode prf . from

class GMapADT mode prf f g where
  gMapADT :: Proxy mode -> Set.Set prf -> f a -> g a

instance GMapADT mode prf U1 U1 where
  gMapADT mode prf = id

instance (GMapADT mode prf f g) => GMapADT mode prf (M1 i c f) (M1 i c g) where
  gMapADT mode prf (M1 c) = M1 (gMapADT mode prf c)

instance (ElimList mode prf f, ElimListM mode prf f ~ g) => GMapADT mode prf (K1 c f) (K1 c g) where
  gMapADT mode prf (K1 c) = K1 (fst (elimList mode prf) c)

instance (GMapADT mode prf f f2, GMapADT mode prf g g2) => GMapADT mode prf (f :*: g) (f2 :*: g2) where
  gMapADT mode prf (f :*: g) = gMapADT mode prf f :*: gMapADT mode prf g

instance (GMapADT mode prf f f2, GMapADT mode prf g g2) => GMapADT mode prf (f :+: g) (f2 :+: g2) where
  gMapADT mode prf (L1 f) = L1 (gMapADT mode prf f)
  gMapADT mode prf (R1 f) = R1 (gMapADT mode prf f)

--------------------------------------------------------------------------------

data Mode (m :: Symbol) = Mode

instance (s ~ s') => IsLabel s (Mode s') where
  fromLabel _ = Mode

-- | Read a protected value.
--
-- The purpose of this library is to be integrated in other libraries that
-- provide access to data in some form. For that purpose, functions like
-- 'read', 'modify' and 'insert' are provided. These functions expect a
-- type level list of permissions in order to infer a type containing
-- fields with possibly eliminated 'Permission' constructors. How this list
-- is generated is up to the calling library.
read :: (ElimList "read" prf a) => Set.Set prf -> a -> (ElimListM "read" prf a)
read prf a = from a
  where (from, _) = elimList (Proxy :: Proxy "read") prf

-- | Modify a protected value.
--
-- The purpose of this library is to be integrated in other libraries that
-- provide access to data in some form. For that purpose, functions like
-- 'read', 'modify' and 'insert' are provided. These functions expect a
-- type level list of permissions in order to infer a type containing
-- fields with possibly eliminated 'Permission' constructors. How this list
-- is generated is up to the calling library.
modify :: (ElimList "modify" prf a) => Set.Set prf -> (ElimListM "modify" prf a -> ElimListM "modify" prf a) -> a -> a
modify prf f = to . f . from
  where (from, to) = elimList (Proxy :: Proxy "modify") prf

-- | Create a protected value.
--
-- The purpose of this library is to be integrated in other libraries that
-- provide access to data in some form. For that purpose, functions like
-- 'read', 'modify' and 'insert' are provided. These functions expect a
-- type level list of permissions in order to infer a type containing
-- fields with possibly eliminated 'Permission' constructors. How this list
-- is generated is up to the calling library.
insert :: (ElimList "insert" prf a) => Set.Set prf -> (ElimListM "insert" prf a) -> a
insert prf a = to a
  where (_, to) = elimList (Proxy :: Proxy "insert") prf
