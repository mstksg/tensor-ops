{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Learn.NeuralNet.AutoEncoder
  ( Encoder(..)
  , encode, decode
  , encoderNet, encodeDecode, testEncoder
  , trainEncoder
  ) where

import           Control.Category
import           Data.Kind
import           Data.Singletons
import           Data.Type.Conjunction
import           Data.Type.Length
import           Data.Type.Product                     as TCP
import           Data.Type.Product.Util                as TCP
import           Data.Type.Sing
import           Prelude hiding                        ((.), id)
import           TensorOps.Learn.NeuralNet.FeedForward
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Family.List
import qualified TensorOps.TOp                         as TO
import qualified TensorOps.Tensor                      as TT

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
encodeDecode e = runNetwork (encoderNet e)

testEncoder
    :: forall t i o. (RealFloat (ElemT t), Tensor t, SingI i)
    => TOp '[ '[i], '[i] ] '[ '[] ]
    -> Encoder t i o
    -> t '[i]
    -> ElemT t
testEncoder loss e = case encoderNet e of
    N _ o p -> TT.unScalar
             . TCP.head'
             . runTOp ( firstOp TO.duplicate
                    >>> secondOp @'[ '[i] ] o
                    >>> TO.swap
                    >>> loss
                      )
             . (:< p)

encoderNet
    :: Encoder t i o
    -> Network t i i
encoderNet (E e d) = e >>> d
{-# INLINE encoderNet #-}

trainEncoder
    :: forall t i o. (Tensor t, RealFloat (ElemT t), SingI i)
    => TOp '[ '[i], '[i] ] '[ '[] ]
    -> ElemT t
    -> t '[i]
    -> Encoder t i o
    -> Encoder t i o
trainEncoder loss r x = \case
    E e d -> case e of
      N sE oE pE -> case d of
        N sD oD pD ->
          let (grE, grD) = encGrad loss x sE oE pE oD pD
              pE' = map1 stepFunc $ zipProd3 (singProd sE) pE grE
              pD' = map1 stepFunc $ zipProd3 (singProd sD) pD grD
          in  E (N sE oE pE') (N sD oD pD')
  where
    stepFunc
        :: forall ns. ()
        => (Sing :&: t :&: t) ns
        -> t ns
    stepFunc !(s :&: p :&: g) =
      TT.zip (\(!p') (!g') -> p' - r * g') p g \\ s
    {-# INLINE stepFunc #-}
{-# INLINE trainEncoder #-}

encGrad
    :: forall k (t :: [k] -> Type) (i :: k) (o :: k) (psE :: [[k]]) (psD :: [[k]]).
     ( Tensor t
     , RealFloat (ElemT t)
     , SingI i
     )
    => TOp '[ '[i], '[i] ] '[ '[] ]
    -> t '[i]
    -> Sing psE
    -> TOp ( '[i] ': psE ) '[ '[o] ]
    -> Prod t psE
    -> TOp ( '[o] ': psD ) '[ '[i] ]
    -> Prod t psD
    -> (Prod t psE, Prod t psD)
encGrad loss x sE oE pE oD pD = splitProd @psD @t @psE lE gr
  where
    lE :: Length psE
    lE = singLength sE
    o :: TOp ('[i] ': psE ++ psD) '[ '[] ]
    o = (\\ lE) $
          firstOp @(psE ++ psD) TO.duplicate
      >>> secondOp @'[ '[i] ] (
            firstOp @psD oE >>> oD
          )
      >>> TO.swap
      >>> loss
    x' :: Prod t ('[i] ': psE ++ psD)
    x' = x :< pE `TCP.append'` pD
    gr :: Prod t (psE ++ psD)
    gr = TCP.tail' $ gradTOp o x'
{-# INLINE encGrad #-}

