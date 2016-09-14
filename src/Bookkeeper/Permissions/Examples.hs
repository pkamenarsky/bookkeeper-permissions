{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Bookkeeper.Permissions.Examples where

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

{-
person :: Person
person = emptyBook
  & #name =: unsafePermission "person"
  & #age  =: unsafePermission 6
  & #bff  =: unsafePermission (emptyBook & #forever =: unsafePermission True)
  & #key  =: unsafePermission "key"

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
