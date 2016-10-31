{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module TensorOps.Learn.NeuralNet.AutoEncoder where

import           Control.Category
import           Data.Kind
import           Data.Type.Product                     as TCP
import           Prelude hiding                        ((.), id)
import           TensorOps.Learn.NeuralNet
import           TensorOps.Learn.NeuralNet.FeedForward
import           TensorOps.Types
import qualified TensorOps.TOp                         as TO

data Encoder :: ([k] -> Type) -> k -> k -> Type where
    E :: { eEncoder :: !(Network t i o)
         , eDecoder :: !(Network t o i)
         } -> Encoder t i o

encode
    :: (RealFloat (ElemT t), Tensor t)
    => Encoder t i o
    -> t '[i]
    -> t '[o]
encode e = runNetwork (eEncoder e)
{-# INLINE encode #-}

decode
    :: (RealFloat (ElemT t), Tensor t)
    => Encoder t i o
    -> t '[o]
    -> t '[i]
decode e = runNetwork (eDecoder e)
{-# INLINE decode #-}

encodeDecode
    :: (RealFloat (ElemT t), Tensor t)
    => Encoder t i o
    -> t '[i]
    -> t '[i]
encodeDecode = \case
    E e d -> runNetwork (e >>> d)

testEncoder
    :: forall t i o. (RealFloat (ElemT t), Tensor t)
    => TOp '[ '[i], '[i] ] '[ '[] ]
    -> Encoder t i o
    -> t '[i]
    -> t '[]
testEncoder loss e x = TCP.head' $
    runTOp loss (encodeDecode e x :< x :< Ø)
