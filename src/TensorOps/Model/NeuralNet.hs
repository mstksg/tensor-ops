{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}

module TensorOps.Model.NeuralNet where

-- import           Data.Type.Remove
import           Data.Singletons
import           Data.Type.Length
import           Data.Type.Uniform
import           TensorOps.Types
import           Type.Class.Known
import qualified TensorOps.TOp       as TO

data Activation k = Act { getAct :: forall (a :: k). SingI a => TensorOp '[ '[a] ] '[ '[a] ] }

actMap
    :: (forall a. Floating a => a -> a)
    -> Activation k
actMap f = Act $ (known, known, TO.map f)
              ~. OPØ

actSoftmax :: Activation k
actSoftmax = Act softmax

logistic :: Floating a => a -> a
logistic x = 1 / (1 + exp (- x))

softmax
    :: SingI i
    => TensorOp '[ '[i] ] '[ '[i] ]
softmax = (known, known, TO.map       exp          )
       ~. (known, known, TO.replicate (US (US UØ)) )
       ~. (known, known, SumRows                   )
       ~. (known, known, TO.map       recip        )
       ~. (known, known, GMul         LZ LZ (LS LZ))
       ~. OPØ

squaredError
    :: forall o. SingI o
    => TensorOp '[ '[o], '[o]] '[ '[] ]
squaredError = (known, known, TO.negate                )
            ~. (known, known, TO.add                   )
            ~. (known, known, TO.replicate (US (US UØ)))
            ~. (known, known, TO.dot                   )
            ~. OPØ

