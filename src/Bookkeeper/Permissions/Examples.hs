{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Bookkeeper.Permissions.Examples where

import Data.Proxy

import Bookkeeper
import Bookkeeper.Internal
import Bookkeeper.Permissions as P

import qualified Data.Type.Map as Map
import qualified Data.Type.Set as Set

data Admin = Admin
data Auth = Auth

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
  ]

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
test_modify = P.modify (Auth `Set.Ext` Set.Empty) undefined (undefined :: Person)
