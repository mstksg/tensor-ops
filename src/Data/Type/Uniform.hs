{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Type.Uniform where

import           Data.Kind
import           Data.Type.Nat
import           Data.Type.Vector
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.Constraint
import           Type.Family.Nat

data Uniform :: a -> [a] -> Type where
    UØ :: Uniform a '[]
    US :: Uniform a as -> Uniform a (a ': as)

uniformLength :: Uniform n ns -> Nat (Len ns)
uniformLength = \case
    UØ   -> Z_
    US u -> S_ (uniformLength u)

-- TODO: Witness instance w/ Nat, for replicate in TensorOps.TOp
instance (m ~ Len ns) => Witness ØC (Known Nat m) (Uniform n ns) where
  (\\) r = \case
    UØ   -> r
    US u -> r \\ u
