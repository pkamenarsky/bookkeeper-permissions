{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Bookkeeper.Permissions.Examples where

import Bookkeeper
import Bookkeeper.Internal
import Bookkeeper.Permissions as P

import Data.Proxy

import qualified Data.Type.Map as Map
import qualified Data.Type.Set as Set

import GHC.Generics

data Admin = Admin
data Auth = Auth

type RobotT = Book '[ "ai" :=> Permission '[ "modify" :=> Admin ] Double ]
type HumanT = Book '[ "ei" :=> Permission '[ "modify" :=> Admin ] Double ]

data PersonType' a b = Robot a | Human b deriving (Show, Generic)

type PersonType = PersonType' RobotT HumanT

type Person = Book
 '[ "name" :=> Permission
      '[ "modify" :=> (Admin :&: Auth)
       , "insert" :=> Auth
       ] String
  , "age"  :=> Permission
      '[ "modify" :=> Auth
       , "insert" :=> Auth
       ] Int
  , "bff"  :=> Permission
      '[ "modify" :=> Admin
       , "insert" :=> Auth
       ] (Book
          '[ "forever" :=> Permission
             '[ "modify" :=> Admin
              , "insert" :=> Auth
              ] Bool
           ])
  , "key" :=> Permission
      '[ "read"   :=> Admin
       , "modify" :=> Admin
       , "insert" :=> Auth
       ] String
  , "type" :=> Permission '[ "modify" :=> Admin ] PersonType
  ]

person :: Person
person = emptyBook
  & #name =: unsafePermission "person"
  & #age  =: unsafePermission 6
  & #bff  =: unsafePermission (emptyBook & #forever =: unsafePermission True)
  & #key  =: unsafePermission "key"
  & #type =: unsafePermission (Robot (emptyBook & #ai =: unsafePermission 200))

{-
test_insert :: Person
test_insert = insert (Auth `Set.Ext` Set.Empty) $ emptyBook
  & #name =: "person"
  & #age  =: 6
  & #bff  =: (emptyBook & #forever =: True)
  & #key  =: "key"

insertKey :: Book' (old Map.:\ "key") -> Book' old
insertKey = undefined

test_insert' :: Person
test_insert' = insertKey $ insert (Auth `Set.Ext` Set.Empty) $ emptyBook
  & #name =: "person"
  & #age  =: 6
  & #bff  =: (emptyBook & #forever =: True)

test_modify :: Person
test_modify = P.modify (Auth `Set.Ext` Set.Empty) f person
  where f p = p & #age =: 6
-}

type Person1 = Book
 '[ "name" :=> Permission
      '[ "modify" :=> Admin ] String
  , "age"  :=> Permission
      '[ "modify" :=> Admin ] Int
  ]

type Person2 = Book
 '[ "name" :=> Permission
      '[ "modify" :=> Auth
       ] String
  , "age"  :=> Int
  ]

type Person3 = Book
 '[ "name" :=> String
  , "age"  :=> Int
  ]

{-
d :: Person3
d = f ((emptyBook & #name =: (unsafePermission "name") & #age =: (unsafePermission (666 :: Int))) :: Person1)
  where
    (f, t) = mapElim (Proxy :: Proxy "modify") (Proxy :: Proxy Admin)
-}

type UndeadT = Book '[ "kills" :=> Permission '[ "read" :=> Admin ] Int ]

data Person0' a = Person0 { _name :: String, _age :: Int }
                | Undead a deriving (Eq, {- Ord, -} Generic, Show)

type Person0 = Person0' UndeadT

data A1 a b c = A1 a | A2 b | A3 c deriving (Show, Generic)

type A1' = A1 Person Person Person

-- d :: _
-- d = mapADT (Proxy :: Proxy "modify") (Admin `Set.Ext` (Auth `Set.Ext` Set.Empty)) (A1 undefined :: A1')

-- d = t (f (A1 person :: A1'))
--   where (f, t) = mapADT (Proxy :: Proxy "modify") (Set.Empty)
-- 
-- d2 = t (f person)
--   where (f, t) = mapADT (Proxy :: Proxy "modify") (Set.Empty)
--
-- d3 = f (undefined :: Person0)
--   where (f, t) = mapADT (Proxy :: Proxy "modify") (Set.Empty)
