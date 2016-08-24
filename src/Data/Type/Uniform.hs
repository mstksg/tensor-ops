{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Data.Type.Uniform where

import           Data.Kind

data Uniform :: a -> [a] -> Type where
    UØ :: Uniform a '[]
    US :: Uniform a as -> Uniform a (a ': as)

