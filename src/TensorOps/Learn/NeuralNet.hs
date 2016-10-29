{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}

module TensorOps.Learn.NeuralNet where

import           Control.Category hiding (id, (.))
import           Data.Singletons
import           Data.Type.Length
import           TensorOps.Types
import qualified TensorOps.TOp    as TO

newtype Activation k
        = Act { getAct
                    :: forall (a :: k). SingI a
                    => TOp '[ '[a] ] '[ '[a] ]
              }

actMap
    :: (forall a. RealFloat a => a -> a)
    -> Activation k
actMap f = Act $ TO.map f

actMap'
    :: (forall a. RealFloat a => a -> a)
    -> (forall a. RealFloat a => a -> a)
    -> Activation k
actMap' f f' = Act $ TO.map' f f'

actSoftmax :: Activation k
actSoftmax = Act softmax

actLogistic :: Activation k
actLogistic = actMap' logistic logistic'

logistic :: Floating a => a -> a
logistic x = 1 / (1 + exp (- x))

logistic' :: Floating a => a -> a
logistic' x = logix * (1 - logix)
  where
    logix = logistic x

softmax
    :: SingI i
    => TOp '[ '[i] ] '[ '[i] ]
softmax = TO.map exp
      >>> TO.duplicate
      >>> firstOp (TO.sumRows >>> TO.map recip)
      >>> TO.outer LZ (LS LZ)

squaredError
    :: forall o. SingI o
    => TOp '[ '[o], '[o]] '[ '[] ]
squaredError = TO.negate
           *>> TO.add
           >>> TO.duplicate
           >>> TO.dot

-- | Second item in stack is the "target"
crossEntropy
    :: forall o. SingI o
    => TOp '[ '[o], '[o]] '[ '[] ]
crossEntropy = TO.map log
           *>> TO.dot
           >>> TO.negate
