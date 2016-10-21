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
  , BLAS(..)
  , Sing(..)
  , SBShape
  , elemsB
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

-- bShapeDims :: BShape a -> [a]
-- bShapeDims (BV x  ) = [x]
-- bShapeDims (BM x y) = [x,y]

class NatKind k => BLAS (b :: BShape k -> Type) where
    type ElemB b :: Type
    liftB
        :: TCV.Vec m (TCV.Vec n (ElemB b) -> ElemB b)
        -> TCV.Vec n (b s)
        -> TCV.Vec m (b s)
    axpy
        :: ElemB b          -- ^ α
        -> b ('BV n)        -- ^ x
        -> Maybe (b ('BV n))  -- ^ y
        -> b ('BV n)        -- ^ α x + y
    dot :: b ('BV n)        -- ^ x
        -> b ('BV n)        -- ^ y
        -> ElemB b          -- ^ x' y
    norm
        :: b ('BV n)        -- ^ x
        -> ElemB b          -- ^ ||x||
    ger :: b ('BV n)        -- ^ x
        -> b ('BV m)        -- ^ y
        -> b ('BM n m)      -- ^ x y'
    gemv
        :: ElemB b          -- ^ α
        -> b ('BM n m)      -- ^ A
        -> b ('BV m)        -- ^ x
        -> Maybe (ElemB b, b ('BV n))        -- ^ β, y
        -> b ('BV n)        -- ^ α A x + β y
    gemm
        :: ElemB b          -- ^ α
        -> b ('BM n o)      -- ^ A
        -> b ('BM o m)      -- ^ B
        -> Maybe (ElemB b, b ('BM n m))      -- ^ β, C
        -> b ('BM n m)      -- ^ α A B + β C
    indexB
        :: Prod (IndexN k) (BShapeDims s)
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
        => (Prod (IndexN k) (BShapeDims s) -> ElemB b -> f (ElemB b))
        -> b s
        -> f (b s)
    -- faster: can we merge bgen and bgenRowsA?
    bgenA
        :: Applicative f
        => (Prod (IndexN k) (BShapeDims s) -> f (ElemB b))
        -> f (b s)
    bgenRowsA
        :: Applicative f
        => (IndexN k n -> f (b ('BV m)))
        -> f (b ('BM n m))
    eye :: b ('BM n n)
    zero :: b s
    zipB
        :: (ElemB b -> ElemB b -> ElemB b)
        -> b s
        -> b s
        -> b s
    -- konstB :: ElemB b -> b s
    traceB
        :: b ('BM n n)
        -> ElemB b
    diagB
        :: b ('BV n)
        -> b ('BM n n)

elemsB
    :: (Applicative f, BLAS b)
    => (ElemB b -> f (ElemB b))
    -> b s
    -> f (b s)
elemsB f = iElemsB (\_ x -> f x)

bgen
    :: forall k (b :: BShape k -> Type) (s :: BShape k). BLAS b
    => (Prod (IndexN k) (BShapeDims s) -> ElemB b)
    -> b s
bgen f = getI $ bgenA (I . f)

bgenRows
    :: BLAS b
    => (IndexN k n -> b ('BV m))
    -> b ('BM n m)
bgenRows f = getI $ bgenRowsA (I . f)

