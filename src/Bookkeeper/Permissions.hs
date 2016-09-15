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

  , mapElim
  , Iso
  , mapADT'
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

class ElimGeneric mode prf f where
  elimGeneric :: Proxy mode -> Proxy prf -> Iso (f a) (ElimM mode prf (f a))

type family ElimM mode prf a where
  ElimM mode prf (Book' kvs) = Book' (ElimBookM mode prf kvs)
  ElimM mode prf x           = x

class Elim mode prf a where
  elim :: Proxy mode -> Proxy prf -> Iso a (ElimM mode prf a)
  {-
  default elim :: (Generic a, ElimGeneric mode prf (Rep a)) => Proxy mode -> Proxy prf -> Iso a (ElimM mode prf a)
  elim mode prf = iso
    undefined
    undefined
  -}

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

--------------------------------------------------------------------------------

data A = A Int Int deriving (Show, Generic)
data B = B Int Int deriving (Show, Generic)
data C = C (Permission '[ "read" :=> (String :|: Double) ] Int) Int deriving (Show, Generic)
data D = D (Permission '[ "read" :=> Double ] Int) Int deriving (Show, Generic)

data E = E A deriving (Show, Generic)
data F = F C deriving (Show, Generic)
data G = G D deriving (Show, Generic)

data DT = X A | Y | Z deriving (Show, Generic)

data PM a b = PM a b deriving (Show, Generic)

{-
class MapElim mode prf a b where
  mapElim :: Proxy mode -> Proxy prf -> Iso a b
  default mapElim :: (Generic a, Generic b, GMapElim mode prf (Rep a) (Rep b)) => Proxy mode -> Proxy prf -> Iso a b
  mapElim mode prf = iso
    (to . fst (gMapElim mode prf) . from)
    (to . snd (gMapElim mode prf) . from)
-}

type family MapRep a where
  MapRep (M1 i c f) = M1 i c (MapRep f)
  MapRep (K1 i (Permission prf c)) = K1 i c
  -- MapRep (K1 i c) = MapRep (Rep c)
  MapRep (K1 i c) = K1 i c
  MapRep (f :*: g) = (MapRep f :*: MapRep g)
  MapRep (f :+: g) = (MapRep f :+: MapRep g)
  MapRep U1 = U1
  MapRep x = x

type family Merge a b where
  Merge (Book' xs) (Book' ys) = Book' (xs Set.:++ ys)
  Merge x y = (x, y)

type family FromRep a where
  FromRep (C1 (MetaCons cn x y) (s1 :*: s2)) = PM (FromRep s1) (FromRep s2)
  FromRep (M1 i c f) = (FromRep f)
  FromRep (K1 i c) = c
  FromRep (f :*: g) = (FromRep f, FromRep g)
  FromRep (f :+: g) = Either (FromRep f) (FromRep g)
  FromRep U1 = ()

-- type family FromRepBook a where
--   FromRepBook (M1 i c f) = (FromRepBook f)
--   FromRepBook (K1 i c) = c
--   FromRepBook (f :*: g) = (FromRepBook f ': FromRepBook g)
--   FromRepBook (f :+: g) = Either (FromRepBook f) (FromRepBook g)
--   FromRepBook U1 = '[]

class GMapElim2 mode prf a where
  gMapElim2 :: Proxy mode -> Proxy prf -> Iso (a p) (MapRep a p)

instance (GMapElim2 mode prf f {-, MapRep (M1 i c f) ~ (M1 i c (MapRep f)) -}) => GMapElim2 mode prf (M1 i c f) where
  gMapElim2 mode prf = iso
    (M1 . fst (gMapElim2 mode prf) . unM1)
    (M1 . snd (gMapElim2 mode prf) . unM1)

instance (MapRep (K1 i (Permission prf c)) ~ (K1 i c)) => GMapElim2 mode prf (K1 i (Permission prf c)) where
  gMapElim2 mode prf = iso
    (\(K1 (Permission a)) -> (K1 a))
    (\(K1 a) -> K1 (Permission a))

-- instance (MapRep (K1 i c) ~ (K1 i c)) => GMapElim2 mode prf (K1 i c) where
--   gMapElim2 mode prf = iso id id

instance (GMapElim2 mode prf a1, GMapElim2 mode prf b1) => GMapElim2 mode prf (a1 :*: b1) where
  gMapElim2 mode prf = iso
    (\(a :*: b) -> fst (gMapElim2 mode prf) a :*: fst (gMapElim2 mode prf) b)
    (\(a :*: b) -> snd (gMapElim2 mode prf) a :*: snd (gMapElim2 mode prf) b)

instance (GMapElim2 mode prf a1, GMapElim2 mode prf b1) => GMapElim2 mode prf (a1 :+: b1) where
  gMapElim2 mode prf = iso
    (\a -> case a of
      L1 a -> L1 (fst (gMapElim2 mode prf) a)
      R1 a -> R1 (fst (gMapElim2 mode prf) a)
    )
    (\a -> case a of
      L1 a -> L1 (snd (gMapElim2 mode prf) a)
      R1 a -> R1 (snd (gMapElim2 mode prf) a)
    )

instance GMapElim2 mode prf U1 where
  gMapElim2 _ _ = iso id id

mapElim :: (Generic a, Generic b, GMapElim2 mode prf (Rep a), Rep b ~ (MapRep (Rep a))) => Proxy mode -> Proxy prf -> Iso a b
mapElim mode prf = iso
  (to . fst (gMapElim2 mode prf) . from)
  (to . snd (gMapElim2 mode prf) . from)

--------------------------------------------------------------------------------

class GMapElim mode prf f g | mode prf f -> g where
  gMapElim :: Proxy mode -> Proxy prf -> Iso (f a) (g b)

instance GMapElim mode prf f g => GMapElim mode prf (M1 i c f) (M1 i c g) where
  gMapElim mode prf = iso
    (M1 . fst (gMapElim mode prf) . unM1)
    (M1 . snd (gMapElim mode prf) . unM1)

instance (GMapElim mode prf a1 a2, GMapElim mode prf b1 b2) => GMapElim mode prf (a1 :*: b1) (a2 :*: b2) where
  gMapElim mode prf = iso
    (\(a :*: b) -> fst (gMapElim mode prf) a :*: fst (gMapElim mode prf) b)
    (\(a :*: b) -> snd (gMapElim mode prf) a :*: snd (gMapElim mode prf) b)

instance (GMapElim mode prf a1 a2, GMapElim mode prf b1 b2) => GMapElim mode prf (a1 :+: b1) (a2 :+: b2) where
  gMapElim mode prf = iso
    (\a -> case a of
      L1 a -> L1 (fst (gMapElim mode prf) a)
      R1 a -> R1 (fst (gMapElim mode prf) a)
    )
    (\a -> case a of
      L1 a -> L1 (snd (gMapElim mode prf) a)
      R1 a -> R1 (snd (gMapElim mode prf) a)
    )

{-
instance GMapElim mode prf (K1 R f) (K1 R f) where
  gMapElim _ _ = iso -- id id
    (\(K1 x) -> (K1 x))
    (\(K1 x) -> (K1 x))
-}

instance {-# OVERLAPPABLE #-} ({-MapRep (Rep f) ~ (Rep g), -} Generic f, Generic g, GMapElim mode prf (Rep f) (Rep g)) => GMapElim mode prf (K1 R f) (K1 R g) where
  gMapElim mode prf = iso
    (\(K1 x) -> (K1 (to (fst (gMapElim mode prf) (from x)))))
    (\(K1 x) -> (K1 (to (snd (gMapElim mode prf) (from x)))))

instance ((ElimTermM prf (Map.Lookup prf' mode)) ~ ()) => GMapElim mode prf (K1 R (Permission prf' a)) (K1 R a) where
  gMapElim _ _ = iso
    (\(K1 (Permission a)) -> (K1 a))
    (\(K1 a) -> K1 (Permission a))

{-
instance ((ElimTermM prf (Map.Lookup prf' mode)) ~ term) => GMapElim mode prf (K1 R (Permission prf' a)) (K1 R (Permission '[ mode :=> term ] a)) where
  gMapElim _ _ = iso
    (\(K1 (Permission a)) -> K1 (Permission a))
    (\(K1 (Permission a)) -> K1 (Permission a))
-}

instance GMapElim mode prf U1 U1 where
  gMapElim _ _ = iso
    (\U1 -> U1)
    (\U1 -> U1)

instance Generic (Book' '[]) where
  type Rep (Book' '[]) = U1
  from _ = U1
  to _   = Book (Map.Empty)

instance (Generic (Book' m)) => Generic (Book' (k :=> v ': m)) where
  type Rep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: Rep (Book' m)
  from (Book (Map.Ext k v m)) = M1 (K1 v) :*: from (Book m)
  to (M1 (K1 v) :*: m) = Book (Map.Ext (Map.Var :: Map.Var k) v (getBook (to m)))

  -- type Rep (Book' (k :=> v ': m)) = S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 v) :*: S1 ('MetaSel ('Just k) 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy) (Rec0 (Book' m))
  -- from (Book (Map.Ext k v m)) = M1 (K1 v) :*: (M1 (K1 (Book m)))
  -- to (M1 (K1 v) :*: (M1 (K1 (Book m)))) = Book (Map.Ext (Map.Var :: Map.Var k) v m)

{-
b :: (Permission '[ "read" :=> Double ] String, String)
b = f (Permission "asd" :: Permission '[ "read" :=> (String :&: Double) ] String, "asd")
  where (f, t) = mapElim (Proxy :: Proxy "read") (Proxy :: Proxy String)
-}

{- 
b :: E
b = f (F (C (Permission 666) 777))
  where (f, t) = mapElim (Proxy :: Proxy "read") (Proxy :: Proxy String)

D1
    ('MetaData "A" "Bookkeeper.Permissions" "main" 'False)
    (C1
       ('MetaCons "A" 'PrefixI 'False)
       (S1
          ('MetaSel
             'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
          (Rec0 Int)
        :*: S1
              ('MetaSel
                 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
              (Rec0 Int)))
    Double
-}

--------------------------------------------------------------------------------

type family MapADTM mode prf a where
  MapADTM mode prf (a b) = (a (ElimListM mode prf b))
  MapADTM mode prf (a b c) = (a (ElimListM mode prf b) (ElimListM mode prf c))
  MapADTM mode prf (a b c d) = (a (ElimListM mode prf b) (ElimListM mode prf c) (ElimListM mode prf d))
  MapADTM mode prf (a b c d e) = (a (ElimListM mode prf b) (ElimListM mode prf c) (ElimListM mode prf d) (ElimListM mode prf e))

mapADT' :: (Generic a, Generic (MapADTM mode prf a ), MapADT mode prf (Rep a) (Rep (MapADTM mode prf a))) => Proxy mode -> Set.Set prf -> a -> MapADTM mode prf a
mapADT' mode prf = to . mapADT mode prf . from

class MapADT mode prf f g where
  mapADT :: Proxy mode -> Set.Set prf -> f a -> g a

instance (ElimList mode prf c, ElimListM mode prf c ~ d) => MapADT mode prf (D1 m (C1 m2 (S1 m3 (K1 m4 c)))) (D1 m (C1 m2 (S1 m3 (K1 m4 d)))) where
  mapADT mode prf (M1 (M1 (M1 (K1 c)))) = (M1 (M1 (M1 (K1 (fst (elimList mode prf) c)))))

