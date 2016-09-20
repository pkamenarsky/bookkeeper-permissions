{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
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

-- * Unsafe
  , unsafePermission
  , unsafeUnpackPermission

-- * Type families & classes
  , MapGeneric
  , MapADTM
  , MapADT
  , mapADT
  ) where

import Prelude hiding (and)

import Data.Typeable

import GHC.TypeLits
import GHC.OverloadedLabels
import GHC.Generics hiding (C, D)

import Data.Proxy
import Data.Type.Bool
import Data.Type.Equality

import GHC.Types (Constraint)

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
  UnpackPermissionM mode prf (Permission '[mode :=> ()] a)           = a
  UnpackPermissionM mode prf (Permission '[mode :=> ModeNotFound] a) = TypeError ('Text "Mode " ':<>: 'ShowType mode ':<>: 'Text " isn't defined for all fields")
  UnpackPermissionM mode prf (Permission prf' a)                     = Permission prf' a

class UnpackPermission mode prf a where
  unpackPermission :: Proxy mode -> Proxy prf -> Iso a (UnpackPermissionM mode prf a)

instance ( UnpackPermissionM mode prf (Permission '[mode :=> ()] a) ~ a
         ) => UnpackPermission mode prf (Permission '[mode :=> ()] a) where
  unpackPermission mode prf = iso (\(Permission a) -> a) (\a -> Permission a)

instance {-# OVERLAPPABLE #-} (UnpackPermissionM mode prf (Permission prf' a) ~ Permission prf' a) => UnpackPermission mode prf (Permission prf' a) where
  unpackPermission _ _ = iso id id

type family ElimPermissionM mode lst a where
  ElimPermissionM mode '[] a        = a
  ElimPermissionM mode (prf:prfs)
                       (Permission prf' v)
                                    = ElimPermissionM mode prfs (UnpackPermissionM mode prf (Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v))
  ElimPermissionM mode (prf:prfs) a = a

class ElimPermission mode t a where
  elimPermission :: Proxy mode -> Set.Set t -> Iso a (ElimPermissionM mode t a)

instance ElimPermission mode '[] a where
  elimPermission _ _ = iso id id

instance ( ElimPermissionM mode (x : xs) (Permission prf' v)
           ~ (ElimPermissionM mode xs (UnpackPermissionM mode x (Permission '[mode :=> (ElimTermM x (Map.Lookup prf' mode))] v)))
         , ElimPermission mode xs (UnpackPermissionM mode x (Permission '[mode :=> (ElimTermM x (Map.Lookup prf' mode))] v))
         , UnpackPermission mode x (Permission '[mode :=> (ElimTermM x (Map.Lookup prf' mode))] v)
         ) => ElimPermission mode (x : xs) (Permission prf' v) where
  elimPermission mode (Set.Ext _ xs) = iso
    (\a -> (fst (elimPermission mode xs)) . (fst (unpackPermission mode (Proxy :: Proxy x))) $ (cnvPermission a :: (Permission '[mode :=> (ElimTermM x (Map.Lookup prf' mode))] v)))
    (\a -> cnvPermission (snd (unpackPermission mode (Proxy :: Proxy x)) (snd (elimPermission mode xs) a) :: (Permission '[mode :=> (ElimTermM x (Map.Lookup prf' mode))] v)))

instance {-# OVERLAPPABLE #-}
         ( ElimPermissionM mode (x : xs) a ~ a
         ) => ElimPermission mode (x : xs) a where
  elimPermission mode _ = iso id id

-- Book ------------------------------------------------------------------------

instance Generic (Book' '[]) where
  type Rep (Book' '[]) = U1
  from _ = U1
  to _   = Book (Map.Empty)

instance (Generic (Book' m)) => Generic (Book' (k :=> v ': m)) where
  type Rep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: Rep (Book' m)
  from (Book (Map.Ext k v m)) = M1 (K1 v) :*: from (Book m)
  to (M1 (K1 v) :*: m) = Book (Map.Ext (Map.Var :: Map.Var k) v (getBook (to m)))

type family Merge a b where
  Merge (Book' xs) (Book' ys) = Book' (xs Set.:++ ys)
  Merge (Book' xs) () = Book' xs
  Merge x y = (x, y)

type family DetBookM mode prf a where
  DetBookM mode prf (Book' (k :=> v ': r)) = Book' '[k :=> MapADTM mode prf (ElimPermissionM mode prf v)] `Merge` DetBookM mode prf (Book' r)
  DetBookM mode prf (Book' '[]) = Book' '[]
  DetBookM mode prf a = a

type instance DetM mode prf (Book' kvs) = DetBookM mode prf (Book' kvs)

-- Other types -----------------------------------------------------------------

type instance DetM mode prf Int = Int
type instance DetM mode prf Char = Char
type instance DetM mode prf Bool = Bool
type instance DetM mode prf Double = Double

-- ADTs ------------------------------------------------------------------------

type family DetM (mode :: Symbol) (prf :: [*]) a

type family MapGenericM mode prf a where
  MapGenericM mode prf (M1 i c f) = M1 i c (MapGenericM mode prf f)
  MapGenericM mode prf (K1 i c)   = K1 i (MapADTM mode prf (ElimPermissionM mode prf c))
  MapGenericM mode prf (f :*: g)  = MapGenericM mode prf f :*: MapGenericM mode prf g
  MapGenericM mode prf (f :+: g)  = MapGenericM mode prf f :+: MapGenericM mode prf g
  MapGenericM mode prf U1         = U1

class MapGeneric mode prf f g | mode prf f -> g where
  mapGeneric :: Proxy mode -> Set.Set prf -> Iso (f x) (g x)

instance (MapGeneric mode prf f g) => MapGeneric mode prf (M1 i c f) (M1 i c g) where
  mapGeneric mode prf = iso
    (\(M1 c) -> M1 (fst (mapGeneric mode prf) c))
    (\(M1 c) -> M1 (snd (mapGeneric mode prf) c))

instance ( MapADTM mode prf (ElimPermissionM mode prf f) ~ g
         , MapADT mode prf (ElimPermissionM mode prf f) g
         , ElimPermission mode prf f
         ) => MapGeneric mode prf (K1 i f) (K1 i g) where
  mapGeneric mode prf = iso
    (\(K1 c) -> K1 (fst (mapADT mode prf) (fst (elimPermission mode prf) c)))
    (\(K1 c) -> K1 (snd (elimPermission mode prf) (snd (mapADT mode prf) c)))

instance (MapGeneric mode prf f f2, MapGeneric mode prf g g2) => MapGeneric mode prf (f :*: g) (f2 :*: g2) where
  mapGeneric mode prf = iso
    (\(f :*: g) -> fst (mapGeneric mode prf) f :*: fst (mapGeneric mode prf) g)
    (\(f :*: g) -> snd (mapGeneric mode prf) f :*: snd (mapGeneric mode prf) g)

instance (MapGeneric mode prf f f2, MapGeneric mode prf g g2) => MapGeneric mode prf (f :+: g) (f2 :+: g2) where
  mapGeneric mode prf = iso
    (\a -> case a of
      (L1 f) -> L1 (fst (mapGeneric mode prf) f)
      (R1 f) -> R1 (fst (mapGeneric mode prf) f)
    )
    (\a -> case a of
      (L1 f) -> L1 (snd (mapGeneric mode prf) f)
      (R1 f) -> R1 (snd (mapGeneric mode prf) f)
    )

instance MapGeneric mode prf U1 U1 where
  mapGeneric mode prf = iso id id

type family MapADTM mode prf a where
  MapADTM mode prf (a b c d e) = (a (MapADTM mode prf b) (MapADTM mode prf c) (MapADTM mode prf d) (MapADTM mode prf e))
  MapADTM mode prf (a b c d) = (a (MapADTM mode prf b) (MapADTM mode prf c) (MapADTM mode prf d))
  MapADTM mode prf (a b c) = (a (MapADTM mode prf b) (MapADTM mode prf c))
  MapADTM mode prf (a b) = a (MapADTM mode prf b)

  MapADTM mode prf a = DetM mode prf a

class (MapADTM mode prf a ~ b) => MapADT mode prf a b where
  mapADT :: Proxy mode -> Set.Set prf -> Iso a (MapADTM mode prf a)

instance {-# OVERLAPPABLE #-}
         ( Generic a, Generic b
         , MapADTM mode prf a ~ b
         , MapGeneric mode prf (Rep a) (Rep b)
         ) => MapADT mode prf a b where
  mapADT mode prf = iso
    (to . fst (mapGeneric mode prf) . from)
    (to . snd (mapGeneric mode prf) . from)

instance (MapADTM mode prf a ~ a) => MapADT mode prf a a where
  mapADT mode prf = iso id id

--------------------------------------------------------------------------------

data Mode (m :: Symbol) = Mode

instance (s ~ s') => IsLabel s (Mode s') where
  fromLabel _ = Mode
