{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module TensorOps.BLAS.HMat where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Data.Type.Product
import           Numeric.LinearAlgebra
import           Numeric.LinearAlgebra.Data as LA
import           TensorOps.BLAS
import qualified Data.Finite                as DF
import qualified Data.Finite.Internal       as DF
import qualified Data.Vector                as V
import qualified Data.Vector.Storable       as VS

data HMat :: Type -> BShape Nat -> Type where
    HMV :: !(Vector a) -> HMat a ('BV n)
    HMM :: !(Matrix a) -> HMat a ('BM n m)

unHMV :: HMat a ('BV n) -> Vector a
unHMV (HMV x) = x

unHMM :: HMat a ('BM n m) -> Matrix a
unHMM (HMM x) = x

instance (Container Vector a, Numeric a) => BLAS (HMat a) where
    type ElemB (HMat a) = a

    axpy α (HMV x) my
        = HMV
        . maybe id (add . unHMV) my
        . scale α
        $ x
    dot (HMV x) (HMV y)
        = x <.> y
    ger (HMV x) (HMV y)
        = HMM $ x `outer` y
    gemv α (HMM a) (HMV x) mβy
        = HMV
        . maybe id (\(β, HMV y) -> add (scale β y)) mβy
        . (a #>)
        . scale α
        $ x
    gemm α (HMM a) (HMM b) mβc
        = HMM
        . maybe id (\(β, HMM c) -> add (scale β c)) mβc
        . (a <>)
        . scale α
        $ b
    indexB = \case
        i :< Ø -> \case
          HMV x -> x `atIndex` fromInteger (DF.getFinite i)
        i :< j :< Ø -> \case
          HMM x -> x `atIndex` ( fromInteger (DF.getFinite i)
                               , fromInteger (DF.getFinite j)
                               )
    indexRowB i (HMM x) = HMV (x ! fromInteger (DF.getFinite i))
    transpB (HMM x) = HMM (tr x)
    iRowsB f (HMM x) = fmap (HMM . fromRows)
                     . traverse (\(i,r) -> unHMV <$> f (DF.Finite i) (HMV r))
                     . zip [0..]
                     . toRows
                     $ x
    iElemsB f = \case
        HMV x -> fmap (HMV . fromList)
               . traverse (\(i,e) -> f (DF.Finite i :< Ø) e)
               . zip [0..]
               . LA.toList
               $ x
        HMM x -> fmap (HMM . fromLists)
               . traverse (\(i,rs) ->
                     traverse (\(j, e) -> f (DF.Finite i :< DF.Finite j :< Ø) e)
                   . zip [0..]
                   $ rs
                 )
               . zip [0..]
               . toLists
               $ x
    -- TODO: can be implemented in parallel maybe?
    bgenA = \case
      SBV sN -> \f -> fmap (HMV . fromList)
                    . traverse (\i -> f (DF.Finite i :< Ø))
                    $ [0 .. fromSing sN - 1]
      SBM sN sM -> \f -> fmap (HMM . fromLists)
                       . traverse (\(i, js) ->
                           traverse (\j -> f (DF.Finite i :< DF.Finite j :< Ø)) js
                         )
                       . zip [0 .. fromSing sM - 1]
                       $ repeat [0 .. fromSing sN - 1]
    bgenRowsA
        :: forall f n m. (Applicative f, SingI n)
        => (DF.Finite n -> f (HMat a ('BV m)))
        -> f (HMat a ('BM n m))
    bgenRowsA f = fmap (HMM . fromRows)
                . traverse (fmap unHMV . f . DF.Finite)
                $ [0 .. fromSing (sing @Nat @n) - 1]
