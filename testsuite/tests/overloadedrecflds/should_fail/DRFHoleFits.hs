{-# LANGUAGE DuplicateRecordFields #-}

module DRFHoleFits where

data T = MkT { foo :: Int }

bar = _ :: T -> Int
