{-# LANGUAGE LambdaCase #-}

module Data.List.Util where

import           Data.List

sum' :: Num a => [a] -> a
sum' = \case
    []       -> 0
    xs@(_:_) -> foldl1' (+) xs
{-# INLINE sum' #-}
