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
  ( ElimM
  , Elim
  , ElimListM
  , ElimList
  ) where

import Prelude hiding (and)

import GHC.TypeLits
import GHC.OverloadedLabels

import Data.Proxy

import Lens.Micro

import Bookkeeper
import Bookkeeper.Internal

import qualified Data.Type.Map as Map
import qualified Data.Type.Set as Set

--------------------------------------------------------------------------------

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
  unpackPermission :: Proxy mode -> Proxy prf -> Lens' a (UnpackPermissionM mode prf a)

instance ( Elim mode prf a
         , UnpackPermissionM mode prf (Permission '[mode :=> ()] a) ~ (ElimM mode prf a)
         ) => UnpackPermission mode prf (Permission '[mode :=> ()] a) where
  unpackPermission mode prf = lens (\(Permission a) -> a ^. elim mode prf) (\(Permission s) a -> Permission (s & elim mode prf .~ a))

instance {-# OVERLAPPABLE #-} (UnpackPermissionM mode prf (Permission prf' a) ~ Permission prf' a) => UnpackPermission mode prf (Permission prf' a) where
  unpackPermission mode prf = lens id (const id)

type family ElimM mode prf a where
  ElimM mode prf (Book' kvs) = Book' (ElimBookM mode prf kvs)
  ElimM mode prf x           = x

class Elim mode prf a where
  elim :: Proxy mode -> Proxy prf -> Lens' a (ElimM mode prf a)

instance (ElimBook mode prf kvs) => Elim mode prf (Book' kvs) where
  elim mode prf = lens (\a -> (a ^. elimBook mode prf)) (\s a -> s & elimBook mode prf .~ a)

instance {-# OVERLAPPABLE #-} (ElimM mode prf a ~ a) => Elim mode prf a where
  elim _ _ = lens id (const id)

type family ElimBookM mode prf a where
  ElimBookM mode prf '[] = '[]
  ElimBookM mode prf ((k :=> Permission prf' v) ': m) = (k :=> UnpackPermissionM mode prf (Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v)) ': ElimBookM mode prf m
  ElimBookM mode prf ((k :=> v) ': m) = (k :=> ElimM mode prf v) ': ElimBookM mode prf m

class ElimBook mode prf a where
  elimBook :: Proxy mode -> Proxy prf -> Lens' (Book' a) (Book' (ElimBookM mode prf a))

instance (ElimBookM mode prf '[] ~ '[]) => ElimBook mode prf '[] where
  elimBook _ _ = lens id (const id)

instance {-# OVERLAPPABLE #-}
    ( UnpackPermission mode prf (Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v)
    , ElimBook mode prf m
    ) => ElimBook mode prf ((k :=> Permission prf' v) ': m) where
  elimBook mode prf = lens
    (\(Book (Map.Ext k v m)) -> Book (Map.Ext k ((cnvPermission v :: (Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v)) ^. unpackPermission mode prf) (getBook (Book m ^. elimBook mode prf))))
    (\(Book (Map.Ext k v m)) (Book (Map.Ext k' v' m')) -> Book (Map.Ext k (cnvPermission ((cnvPermission v :: (Permission '[mode :=> (ElimTermM prf (Map.Lookup prf' mode))] v)) & unpackPermission mode prf .~ v')) (getBook (Book m & elimBook mode prf .~ Book m'))))

instance {-# OVERLAPPABLE #-}
    ( Elim mode prf v
    , ElimBook mode prf m
    , ElimBookM mode prf ((k :=> v) ': m) ~ ((k :=> ElimM mode prf v) ': ElimBookM mode prf m)
    ) => ElimBook mode prf ((k :=> v) ': m) where
  elimBook mode prf = lens
    (\(Book (Map.Ext k v m)) -> (Book (Map.Ext k (v ^. elim mode prf) (getBook (Book m ^. elim mode prf)))))
    (\(Book (Map.Ext k v m)) (Book (Map.Ext k' v' m')) -> Book (Map.Ext k (v & elim mode prf .~ v') (getBook (Book m & elim mode prf .~ Book m'))))

type family ElimListM mode lst a where
  ElimListM mode '[] a    = a
  ElimListM mode (x:xs) a = ElimListM mode xs (ElimM mode x a)

class ElimList mode t a where
  elimList :: Proxy mode -> Set.Set t -> Lens' a (ElimListM mode t a)

instance ElimList mode '[] a where
  elimList _ _ = lens id (const id)

instance (Elim mode x a, ElimList mode xs (ElimM mode x a)) => ElimList mode (x : xs) a where
  elimList mode (Set.Ext x xs) = lens
    (\a -> a ^. (elim mode (Proxy :: Proxy x) . elimList mode xs))
    (\s a -> s & (elim mode (Proxy :: Proxy x) . elimList mode xs) .~ a)

--------------------------------------------------------------------------------

data Mode (m :: Symbol) = Mode

instance (s ~ s') => IsLabel s (Mode s') where
  fromLabel _ = Mode

modify :: forall prf mode a. ElimList mode prf a => Mode mode -> Set.Set prf -> (ElimListM mode prf a -> ElimListM mode prf a) -> a -> a
modify _ prf f a = over (elimList (Proxy :: Proxy mode) prf) f a
