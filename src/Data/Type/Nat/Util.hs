{-# LANGUAGE RankNTypes #-}

module Data.Type.Nat.Util where

import           Data.Type.Nat

withNat
    :: Integer
    -> (forall n. Nat n -> Maybe r)
    -> Maybe r
withNat x f = case compare x 0 of
    LT -> Nothing
    EQ -> f Z_
    GT -> withNat (x - 1) (f . S_)
