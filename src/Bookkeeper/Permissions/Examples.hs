{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Bookkeeper.Permissions.Examples where

import Data.Proxy

import Bookkeeper
import Bookkeeper.Permissions as P

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
              , "insert" :=> Auth] Bool
           ])
  , "complex" :=> Permission
      '[ "read"   :=> Admin
       , "modify" :=> Admin
       , "insert" :=> Auth
       ] Double
  ]

test_insert :: Person
test_insert = insert (Auth `Set.Ext` Set.Empty) $ emptyBook
  & #name     =: "person"
  & #age      =: 6
  & #bff      =: (emptyBook & #forever =: True)
  & #complex  =: 6

test_modify :: Person
test_modify = P.modify (Auth `Set.Ext` Set.Empty) undefined (undefined :: Person)
