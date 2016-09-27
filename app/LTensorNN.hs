{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

import           Control.Category
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List   (Sing(..))
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Product              as TCP
import           Data.Type.Sing
import           Data.Type.Uniform
import           GHC.TypeLits
import           Prelude hiding                 ((.), id)
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import           System.Random.MWC
import           TensorOps.LTensor
import           TensorOps.Types
import           Type.Class.Known
import           Type.Family.List
import qualified TensorOps.TOp                  as TO


ffLayer'
    :: (SingI i, SingI o)
    => TensorOp '[ '[i], '[o,i], '[o]] '[ '[o] ]
ffLayer' = (LS (LS LZ), known, Shuffle (IS IZ :< IZ :< Ø))
        ~. (known     , known, GMul    (LS LZ) (LS LZ) LZ)
        ~. (known     , known, TO.zip2 (+)               )
        ~. OPØ

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { nsOs     :: Sing os
         , nOp      :: TensorOp ('[i] ': os) '[ '[o] ]
         , nParams  :: Prod t os
         } -> Network t i o

(~*.)
    :: (SingI a, SingI b)
    => Network t a b
    -> Network t b c
    -> Network t a c
N sOs1 o1 p1 ~*. N sOs2 o2 p2 =
    N (sOs1 %:++ sOs2)
      (pappend (sing `SCons` sOs1) sing sOs2 o1 o2)
      (p1 `TCP.append'` p2)

ffLayer
    :: forall o i m t. (SingI o, SingI i, PrimMonad m, Tensor t)
    => Gen (PrimState m)
    -> m (Network t i o)
ffLayer g = (\w b -> N sing ffLayer' (w :< b :< Ø))
        <$> genRand (normalDistr 0 0.5) g
        <*> genRand (normalDistr 0 0.5) g

main :: IO ()
main = print 1
