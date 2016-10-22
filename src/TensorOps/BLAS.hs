{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module TensorOps.BLAS
  ( BShape(..)
  , BShapeDims
  , BShapeP(..)
  , bShapeProd, pbvProd, pbmProd
  , BLAS(..)
  , Sing(..)
  , SBShape
  , elemsB
  , zipB
  , bgen
  , bgenRows
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude hiding (Reverse, Head, sReverse, (:-))
import           Data.Singletons.TH
import           Data.Type.Combinator
import           Data.Type.Product              as TCP
import           Data.Type.Sing
import           Data.Type.Vector               (VecT(..), Vec)
import           TensorOps.NatKind
import qualified Data.Type.Vector               as TCV

$(singletons [d|
  data BShape a = BV !a | BM !a !a
    deriving (Show, Eq, Ord, Functor)
  |])

type family BShapeDims (s :: BShape k) = (ks :: [k]) | ks -> s where
    BShapeDims ('BV x  ) = '[x]
    BShapeDims ('BM x y) = '[x,y]

genDefunSymbols [''BShapeDims]

data BShapeP :: (k -> Type) -> BShape k -> Type where
    PBV :: { unPBV :: !(f a) } -> BShapeP f ('BV a)
    PBM :: { unPBMn :: f a
           , unPBMm :: f b
           } -> BShapeP f ('BM a b)

-- TODO: rewrite rules
bShapeProd
    :: BShapeP f s
    -> Prod f (BShapeDims s)
bShapeProd = \case
    PBV x   -> x :< Ø
    PBM x y -> x :< y :< Ø

pbvProd
    :: BShapeP f ('BV a)
    -> Prod f '[a]
pbvProd (PBV x) = x :< Ø

pbmProd
    :: BShapeP f ('BM a b)
    -> Prod f '[a,b]
pbmProd (PBM x y) = x :< y :< Ø

-- bShapeDims :: BShape a -> [a]
-- bShapeDims (BV x  ) = [x]
-- bShapeDims (BM x y) = [x,y]

class NatKind k => BLAS (b :: BShape k -> Type) where
    type ElemB b :: Type
    liftB
        :: Sing s
        -> Vec m (Vec n (ElemB b) -> ElemB b)
        -> Vec n (b s)
        -> Vec m (b s)
    axpy
        :: ElemB b          -- ^ α
        -> b ('BV n)        -- ^ x
        -> Maybe (b ('BV n))  -- ^ y
        -> b ('BV n)        -- ^ α x + y
    dot :: b ('BV n)        -- ^ x
        -> b ('BV n)        -- ^ y
        -> ElemB b          -- ^ x' y
    -- norm
    --     :: b ('BV n)        -- ^ x
    --     -> ElemB b          -- ^ ||x||
    ger :: b ('BV n)        -- ^ x
        -> b ('BV m)        -- ^ y
        -> b ('BM n m)      -- ^ x y'
    gemv
        :: ElemB b          -- ^ α
        -> b ('BM n m)      -- ^ A
        -> b ('BV m)        -- ^ x
        -> Maybe (ElemB b, b ('BV n))        -- ^ β, y
        -> b ('BV n)        -- ^ α A x + β y
    -- TODO: better way to scale matrices
    gemm
        :: ElemB b          -- ^ α
        -> b ('BM n o)      -- ^ A
        -> b ('BM o m)      -- ^ B
        -> Maybe (ElemB b, b ('BM n m))      -- ^ β, C
        -> b ('BM n m)      -- ^ α A B + β C
    indexB
        :: BShapeP (IndexN k) s
        -> b s
        -> ElemB b
    indexRowB
        :: IndexN k n
        -> b ('BM n m)
        -> b ('BV m)
    transpB
        :: b ('BM n m)
        -> b ('BM m n)
    iRowsB
        :: Applicative f
        => (IndexN k n -> b ('BV m) -> f (b ('BV o)))
        -> b ('BM n m)
        -> f (b ('BM n o))
    iElemsB
        :: Applicative f
        => (BShapeP (IndexN k) s -> ElemB b -> f (ElemB b))
        -> b s
        -> f (b s)
    -- TODO: can we merge bgen and bgenRowsA?
    bgenA
        :: Applicative f
        => Sing s
        -> (BShapeP (IndexN k) s -> f (ElemB b))
        -> f (b s)
    bgenRowsA
        :: (Applicative f, SingI n)
        => (IndexN k n -> f (b ('BV m)))
        -> f (b ('BM n m))
    eye :: Sing n
        -> b ('BM n n)
    traceB
        :: b ('BM n n)
        -> ElemB b
    diagB
        :: b ('BV n)
        -> b ('BM n n)
    getDiagB
        :: b ('BM n n)
        -> b ('BV n)
    -- zero :: b s

elemsB
    :: (Applicative f, BLAS b)
    => (ElemB b -> f (ElemB b))
    -> b s
    -> f (b s)
elemsB f = iElemsB (\_ x -> f x)
{-# INLINE elemsB #-}

bgen
    :: forall k (b :: BShape k -> Type) (s :: BShape k). BLAS b
    => Sing s
    -> (BShapeP (IndexN k) s -> ElemB b)
    -> b s
bgen s f = getI $ bgenA s (I . f)
{-# INLINE bgen #-}

bgenRows
    :: (BLAS b, SingI n)
    => (IndexN k n -> b ('BV m))
    -> b ('BM n m)
bgenRows f = getI $ bgenRowsA (I . f)
{-# INLINE bgenRows #-}

zipB
    :: BLAS b
    => Sing s
    -> (ElemB b -> ElemB b -> ElemB b)
    -> b s
    -> b s
    -> b s
zipB s f x y = getI . TCV.head'
             $ liftB s (I (\(I x' :* I y' :* ØV) -> f x' y') :* ØV)
                       (I x :* I y :* ØV)
{-# INLINE zipB #-}
