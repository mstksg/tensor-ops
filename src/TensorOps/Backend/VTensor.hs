{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType     #-}

module TensorOps.Backend.VTensor where

import           Data.Kind
import           GHC.TypeLits
import qualified Data.Vector  as V

data Vec :: Nat -> Type -> Type where
    V :: { getV :: V.Vector a }
      -> Vec n a

-- data NestedVec :: [Nat] -> Type -> Type where
--     NVZ :: !a -> NestedVec '[]  a
--     NVS :: VecT n (NestedVec ns) a -> NestedVec (n ': ns) a
