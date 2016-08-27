{-# LANGUAGE GADTs         #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Vector.Util where

import           Data.Type.Nat
import           Data.Bifunctor
import           Data.Type.Vector
import           Type.Family.Nat


splitVec
    :: Nat n
    -> VecT (n + m) f a
    -> (VecT n f a, VecT m f a)
splitVec = \case
    Z_   -> (ØV,)
    S_ n -> \case
      x :* xs -> first (x :*) (splitVec n xs)
