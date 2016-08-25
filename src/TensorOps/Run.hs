{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Run where

import           Control.Arrow                       ((&&&))
import           Data.Bifunctor
import           Data.Functor.Identity
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Length)
import           Data.Type.Length
import           Data.Type.Product hiding            (append')
import           Data.Type.Uniform
import           TensorOps.Tensor
import           TensorOps.Types
import           Type.Class.Known

runTOp
    :: (Tensor t, Floating (ElemT t))
    => TOp ns ms
    -> Prod t ns
    -> Prod t ms
runTOp = \case
    Lift uNs uMs f -> liftT uNs uMs f
    MatMat c       -> only . mulChain c
    MatVec         -> \case
      x :< y :< Ø  -> only (x `mulMV` y)
    Outer          -> \case
      x :< y :< Ø  -> only (x `outer` y)
    Transp r is    -> only . transp r is . head'
    Fold f         -> only . foldT f     . head'

runTensorOp
    :: forall t ns ms. (Tensor t, Floating (ElemT t))
    => TensorOp ns ms
    -> Prod t ns
    -> Prod t ms
runTensorOp = \case
    OPØ      -> id
    OP1 o    -> runTOp o
    oL :. oR -> runTensorOp oR . runTensorOp oL
    oL :* oR -> overProdSplit known (runTensorOp oL) (runTensorOp oR)
    oL :& oR -> uncurry append' . (runTensorOp oL &&& runTensorOp oR)

splitProd
    :: Sing ns
    -> Prod f (ns :++ ms)
    -> (Prod f ns, Prod f ms)
splitProd = \case
    SNil         -> \p -> (Ø, p)
    _ `SCons` sNs -> \case
      x :< xs -> case splitProd sNs xs of
                   (xs', ys) -> (x :< xs', ys)

append'
    :: Prod f as
    -> Prod f bs
    -> Prod f (as :++ bs)
append' = \case
    Ø       -> id
    x :< xs -> (x :<) . append' xs

overProdInit
    :: Length ns
    -> Length os
    -> (Prod g ns -> Prod g ms)
    -> Prod g (ns :++ os)
    -> Prod g (ms :++ os)
overProdInit lN lO f = runIdentity . prodInit lN lO (Identity . f)

prodInit
    :: Functor f
    => Length ns
    -> Length os
    -> (Prod g ns -> f (Prod g ms))
    -> Prod g (ns :++ os)
    -> f (Prod g (ms :++ os))
prodInit lN lO f = case lN of
    LZ     -> \xs -> (`append'` xs) <$> f Ø
    LS lN' -> \case
      x :< xs -> prodInit lN' lO (\xs' -> f (x :< xs')) xs

overProdSplit
    :: Length ns
    -> (Prod g ns -> Prod g ms)
    -> (Prod g os -> Prod g ps)
    -> Prod g (ns :++ os)
    -> Prod g (ms :++ ps)
overProdSplit lN f g = runIdentity . prodSplit lN (Identity . f) (Identity . g)

prodSplit
    :: Applicative f
    => Length ns
    -> (Prod g ns -> f (Prod g ms))
    -> (Prod g os -> f (Prod g ps))
    -> Prod g (ns :++ os)
    -> f (Prod g (ms :++ ps))
prodSplit lN f g = case lN of
    LZ     -> \xs -> append' <$> f Ø <*> g xs
    LS lN' -> \case
      x :< xs -> prodSplit lN' (\xs' -> f (x :< xs')) g xs

