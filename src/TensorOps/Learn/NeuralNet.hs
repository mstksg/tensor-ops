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
{-# INLINE actMap #-}

actMap'
    :: (forall a. RealFloat a => a -> a)
    -> (forall a. RealFloat a => a -> a)
    -> Activation k
actMap' f f' = Act $ TO.map' f f'
{-# INLINE actMap' #-}

actSoftmax :: Activation k
actSoftmax = Act softmax
{-# INLINE actSoftmax #-}

actLogistic :: Activation k
actLogistic = actMap' logistic logistic'
{-# INLINE actLogistic #-}

logistic :: Floating a => a -> a
logistic x = 1 / (1 + exp (- x))
{-# INLINE logistic #-}

logistic' :: Floating a => a -> a
logistic' x = logix * (1 - logix)
  where
    logix = logistic x
{-# INLINE logistic' #-}

softmax
    :: SingI i
    => TOp '[ '[i] ] '[ '[i] ]
softmax = TO.map exp
      >>> TO.duplicate
      >>> firstOp (TO.sumRows >>> TO.map recip)
      >>> TO.outer LZ (LS LZ)
{-# INLINE softmax #-}

squaredError
    :: forall o. SingI o
    => TOp '[ '[o], '[o]] '[ '[] ]
squaredError = TO.negate
           *>> TO.add
           >>> TO.duplicate
           >>> TO.dot
{-# INLINE squaredError #-}

-- | Second item in stack is the "target"
crossEntropy
    :: forall o. SingI o
    => TOp '[ '[o], '[o]] '[ '[] ]
crossEntropy = TO.map log
           *>> TO.dot
           >>> TO.negate
{-# INLINE crossEntropy #-}
