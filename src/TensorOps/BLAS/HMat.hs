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

module TensorOps.BLAS.HMat
  ( HMat
  ) where

import           Control.DeepSeq
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Data.Type.Combinator
import           Data.Type.Vector            (Vec, VecT(..))
import           Data.Type.Vector.Util       (curryV2', curryV3')
import           Numeric.LinearAlgebra
import           Numeric.LinearAlgebra.Data  as LA
import           Numeric.LinearAlgebra.Devel
import           TensorOps.BLAS
import           Type.Class.Higher.Util
import qualified Data.Finite                 as DF
import qualified Data.Finite.Internal        as DF
import qualified Data.Vector.Storable        as VS

data HMat :: Type -> BShape Nat -> Type where
    HMV :: { unHMV :: !(Vector a) } -> HMat a ('BV n)
    HMM :: { unHMM :: !(Matrix a) } -> HMat a ('BM n m)

instance (VS.Storable a, NFData a) => NFData (HMat a s) where
    rnf = \case
      HMV xs -> rnf xs
      HMM xs -> rnf xs
    {-# INLINE rnf #-}

instance (VS.Storable a, NFData a) => NFData1 (HMat a)

liftB'
    :: (Numeric a)
    => Sing s
    -> (Vec n a -> a)
    -> Vec n (HMat a s)
    -> HMat a s
liftB' s f xs = bgen s $ \i -> f (indexB i <$> xs)
{-# INLINE liftB' #-}

instance (Container Vector a, Numeric a) => BLAS (HMat a) where
    type ElemB (HMat a) = a

    -- TODO: rewrite rules
    -- write in parallel?
    liftB
        :: forall n m s. ()
        => Sing s
        -> Vec m (Vec n a -> a)
        -> Vec n (HMat a s)
        -> Vec m (HMat a s)
    liftB s fs xs = fmap go fs
      where
        go :: (Vec n a -> a) -> HMat a s
        go f = case xs of
          ØV -> case s of
            SBV sN    -> HMV $ konst (f ØV) ( fromIntegral (fromSing sN) )
            SBM sN sM -> HMM $ konst (f ØV) ( fromIntegral (fromSing sN)
                                            , fromIntegral (fromSing sM)
                                            )
          I x :* ØV -> case x of
            HMV x' -> HMV (cmap (f . (:* ØV) . I) x')
            HMM x' -> HMM (cmap (f . (:* ØV) . I) x')
          I x :* I y :* ØV -> case x of
            HMV x' -> case y of
              HMV y' -> HMV $ VS.zipWith (curryV2' f) x' y'
            HMM x' -> case y of
              HMM y' -> HMM $ liftMatrix2 (VS.zipWith (curryV2' f)) x' y'
          I x :* I y :* I z :* ØV -> case x of
            HMV x' -> case y of
              HMV y' -> case z of
                HMV z' -> HMV $ VS.zipWith3 (curryV3' f) x' y' z'
            _ -> liftB' s f xs
          _ -> liftB' s f xs

    axpy α (HMV x) my
        = HMV
        . maybe id (add . unHMV) my
        . scale α
        $ x
    {-# INLINE axpy #-}
    dot (HMV x) (HMV y)
        = x <.> y
    {-# INLINE dot #-}
    ger (HMV x) (HMV y)
        = HMM $ x `outer` y
    {-# INLINE ger #-}
    gemv α (HMM a) (HMV x) mβy
        = HMV
        . maybe id (\(β, HMV y) -> add (scale β y)) mβy
        . (a #>)
        . scale α
        $ x
    {-# INLINE gemv #-}
    gemm α (HMM a) (HMM b) mβc
        = HMM
        . maybe id (\(β, HMM c) -> add (scale β c)) mβc
        . (a <>)
        . scale α
        $ b
    {-# INLINE gemm #-}
    indexB = \case
        PBV i -> \case
          HMV x -> x `atIndex` fromInteger (DF.getFinite i)
        PBM i j -> \case
          HMM x -> x `atIndex` ( fromInteger (DF.getFinite i)
                               , fromInteger (DF.getFinite j)
                               )
    {-# INLINE indexB #-}
    indexRowB i (HMM x) = HMV (x ! fromInteger (DF.getFinite i))
    {-# INLINE indexRowB #-}
    transpB (HMM x) = HMM (tr x)
    {-# INLINE transpB #-}
    iRowsB f (HMM x) = fmap (HMM . fromRows)
                     . traverse (\(i,r) -> unHMV <$> f (DF.Finite i) (HMV r))
                     . zip [0..]
                     . toRows
                     $ x
    {-# INLINE iRowsB #-}
    iElemsB f = \case
        HMV x -> fmap (HMV . fromList)
               . traverse (\(i,e) -> f (PBV (DF.Finite i)) e)
               . zip [0..]
               . LA.toList
               $ x
        HMM x -> fmap (HMM . fromLists)
               . traverse (\(i,rs) ->
                     traverse (\(j, e) -> f (PBM (DF.Finite i) (DF.Finite j)) e)
                   . zip [0..]
                   $ rs
                 )
               . zip [0..]
               . toLists
               $ x
    {-# INLINE iElemsB #-}
    -- TODO: can be implemented in parallel maybe?
    bgenA = \case
      SBV sN -> \f -> fmap (HMV . fromList)
                    . traverse (\i -> f (PBV (DF.Finite i)))
                    $ [0 .. fromSing sN - 1]
      SBM sN sM -> \f -> fmap (HMM . fromLists)
                       . traverse (\(i, js) ->
                           traverse (\j -> f (PBM (DF.Finite i) (DF.Finite j))) js
                         )
                       . zip [0 .. fromSing sN - 1]
                       $ repeat [0 .. fromSing sM - 1]
    {-# INLINE bgenA #-}
    bgenRowsA
        :: forall f n m. (Applicative f, SingI n)
        => (DF.Finite n -> f (HMat a ('BV m)))
        -> f (HMat a ('BM n m))
    bgenRowsA f = fmap (HMM . fromRows)
                . traverse (fmap unHMV . f . DF.Finite)
                $ [0 .. fromSing (sing @Nat @n) - 1]
    {-# INLINE bgenRowsA #-}

    eye = HMM . ident . fromIntegral . fromSing
    {-# INLINE eye #-}
    diagB = HMM . diag . unHMV
    {-# INLINE diagB #-}
    getDiagB = HMV . takeDiag . unHMM
    {-# INLINE getDiagB #-}
    traceB = sumElements . takeDiag . unHMM
    {-# INLINE traceB #-}
