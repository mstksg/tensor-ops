{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}

module TensorOps.Learn.NeuralNet where

-- import           Data.Type.Remove
-- import           Data.Type.Uniform
import           Data.Singletons
import           Data.Type.Length
import           TensorOps.Types
import           Type.Class.Known
import qualified TensorOps.TOp        as TO

data Activation k = Act { getAct :: forall (a :: k). SingI a => TensorOp '[ '[a] ] '[ '[a] ] }

actMap
    :: (forall a. RealFloat a => a -> a)
    -> Activation k
actMap f = Act $ (known, known, TO.map f)
              ~. OPØ

actMap'
    :: (forall a. RealFloat a => a -> a)
    -> (forall a. RealFloat a => a -> a)
    -> Activation k
actMap' f f' = Act $ (known, known, TO.map' f f')
                  ~. OPØ

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
    => TensorOp '[ '[i] ] '[ '[i] ]
softmax = (known, known, TO.map       exp          )
       ~. (known, known, TO.duplicate              )
       ~. (known, known, SumRows                   )
       ~. (known, known, TO.map       recip        )
       ~. (known, known, GMul         LZ LZ (LS LZ))
       ~. OPØ

squaredError
    :: forall o. SingI o
    => TensorOp '[ '[o], '[o]] '[ '[] ]
squaredError = (known, known, TO.negate   )
            ~. (known, known, TO.add      )
            -- ~. (known, known, TO.map (**2))
            -- ~. (known, known, SumRows     )
            ~. (known, known, TO.duplicate)
            ~. (known, known, TO.dot      )
            ~. OPØ

-- | Second item in stack is the "target"
crossEntropy
    :: forall o. SingI o
    => TensorOp '[ '[o], '[o]] '[ '[] ]
-- crossEntropy = (known, known, TO.map log)
--             ~. (known, known, TO.dot    )
--             ~. (known, known, TO.negate )
--             ~. OPØ
crossEntropy = (known, known, TO.zip f )
            ~. (known, known, SumRows  )
            ~. OPØ
  where
    f :: forall a. RealFloat a => a -> a -> a
    f p q | q <= 0    = 0
          | p <= 0    = error "hey why is p <= 0"
          | otherwise = - log p * q
          -- | otherwise = log (1/p) * q

