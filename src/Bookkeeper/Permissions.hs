{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Bookkeeper.Permissions
  (
-- * Preamble
--
-- | This experimental library adds permissions to
-- <https://hackage.haskell.org/package/bookkeeper bookkeeper> records.
--
-- A common pattern in user facing programs is the following:
--
-- > doAdminStuff admin = do
-- >   when admin $ do
-- >    ...
--
-- But this is not enforced by the type system and thus can easily be forgotten
-- or gotten wrong. <https://hackage.haskell.org/package/lio One approach> to
-- getting the type system work for us is by marking specific regions of code as
-- requiring a specific /security policy/, and not allowing code with a lower
-- security policy to call code with a higher security policy.
--
-- The approach that this library takes is to require /data/ being marked with
-- /permissions/ that need to be /proven/ when accessing said data.
--
-- The general idea is to mark record fields as requiring specific permissions:
--
-- > data Admin = Admin
-- > data Auth  = Auth
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
-- A 'Permission' definition has the following form:
--
-- > Permission [ mode :=> permissions, mode2 :=> permissions2 ] type
--
-- Different permissions can be mixed with the ':|:' and ':&:' operators, i.e:
--
-- > Permission [ "modify" :=> (Admin :&: Auth)]
--
-- Now, when modifying a record a list of permissions needs to be provided as
-- well:
--
-- > modify (Auth `Set.Ext` Set.Empty) f person
-- >   where f = ...
--
-- The provided list of permissions is used to /eliminate/ the 'Permission'
-- constructor from all fields that require less or equal permissions to those
-- provided in the permissions list.
--
-- For example, the above list of '[Auth] would eliminate the 'Permission'
-- constructor from the field "age", but would leave the type of "name" as
--
-- > Permission [ "modify" :=> Admin ] String
--
-- meaning that it can't be accessed without providing the permission 'Admin'.
--
--
    Permission
  , (:|:), (:&:)
  , modify
  , insert
  ) where

import Prelude hiding (and)

import GHC.TypeLits
import GHC.OverloadedLabels

import Data.Proxy

import Bookkeeper hiding (modify)
import Bookkeeper.Internal hiding (modify)

import qualified Data.Type.Map as Map
import qualified Data.Type.Set as Set

--------------------------------------------------------------------------------

type Iso a b = (a -> b, b -> a)

iso :: (a -> b) -> (b -> a) -> Iso a b
iso = (,)

data Star

data a :|: b
data a :&: b
data a :*: b

data Permission pr a = Permission a deriving Show

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
  ElimTermM Star x              = ()
  ElimTermM prf (Just (op x y)) = ElimTerm1M prf (op (ElimTermM prf  (Just x)) (ElimTermM prf  (Just y)))
  ElimTermM prf (Just x)        = ElimTerm1M prf x
  ElimTermM prf Nothing         = ModeNotFound

--------------------------------------------------------------------------------

cnvPermission :: Permission prf a -> Permission prf' a
cnvPermission (Permission a) = Permission a

type family UnpackPermissionM mode prf a where
  UnpackPermissionM mode prf (Permission '[mode :=> ()] a)           = ElimM mode prf a
  UnpackPermissionM mode prf (Permission '[mode :=> ModeNotFound] a) = TypeError (Text "Mode " :<>: ShowType mode :<>: Text " isn't defined for all fields")
  UnpackPermissionM mode prf (Permission prf' a)                     = Permission prf' a

class UnpackPermission mode prf a where
  unpackPermission :: Proxy mode -> Proxy prf -> Iso a (UnpackPermissionM mode prf a)

instance ( Elim mode prf a
         , UnpackPermissionM mode prf (Permission '[mode :=> ()] a) ~ (ElimM mode prf a)
         ) => UnpackPermission mode prf (Permission '[mode :=> ()] a) where
  unpackPermission mode prf = iso (\(Permission a) -> fst (elim mode prf) a) (\a -> Permission (snd (elim mode prf) a))

instance {-# OVERLAPPABLE #-} (UnpackPermissionM mode prf (Permission prf' a) ~ Permission prf' a) => UnpackPermission mode prf (Permission prf' a) where
  unpackPermission mode prf = iso id id

type family ElimM mode prf a where
  ElimM mode prf (Book' kvs) = Book' (ElimBookM mode prf kvs)
  ElimM mode prf x           = x

class Elim mode prf a where
  elim :: Proxy mode -> Proxy prf -> Iso a (ElimM mode prf a)

instance (ElimBook mode prf kvs) => Elim mode prf (Book' kvs) where
  elim mode prf = iso (\a -> fst (elimBook mode prf) a) (\a -> snd (elimBook mode prf) a)

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
  elimList mode (Set.Ext x xs) = iso
    ((fst (elimList mode xs)) . (fst (elim mode (Proxy :: Proxy x))))
    ((snd (elim mode (Proxy :: Proxy x))) . (snd (elimList mode xs)))

--------------------------------------------------------------------------------

data Mode (m :: Symbol) = Mode

instance (s ~ s') => IsLabel s (Mode s') where
  fromLabel _ = Mode

modify :: (ElimList "modify" prf a) => Set.Set prf -> (ElimListM "modify" prf a -> ElimListM "modify" prf a) -> a -> a
modify prf f = to . f . from
  where (from, to) = elimList (Proxy :: Proxy "modify") prf

insert :: (ElimList "insert" prf a) => Set.Set prf -> (ElimListM "insert" prf a) -> a
insert prf a = to a
  where (_, to) = elimList (Proxy :: Proxy "insert") prf
