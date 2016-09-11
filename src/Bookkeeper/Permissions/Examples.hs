{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Bookkeeper.Permissions.Examples where

import Bookkeeper
import Bookkeeper.Permissions

data Admin
data Auth

type PersonB = Book
 '[ "name" :=> Permission '["read" :=> (Admin :&: Auth)] String
  , "age"  :=> Permission '["read" :=> Auth] Int
  , "bff"  :=> Permission '["read" :=> Admin] (Book
    '[ "forever" :=> Permission '["read" :=> Admin] Bool ])
  , "complex" :=> Permission '["read" :=> Admin, "modify" :=> Admin] Double
  ]
