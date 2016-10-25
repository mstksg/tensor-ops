{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module TensorOps.Tensor
  ( konst
  , map
  , zipN
  , zip
  , zip3
  , add
  , gradLift
  -- , gradLift1
  -- , gradLift1N
  , inner, outer, outerV, dot, matVec, vecMat, matMat
  , fromList, generate, rows, toRows
  , ixElems, elems, itoList, toList, unScalar
  ) where

import           Control.Applicative
import           Control.Monad.Trans.State.Strict
import           Data.Functor
import           Data.Kind
import           Data.List hiding                 ((\\), zip, map, zip3)
import           Data.Monoid
import           Data.Proxy
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Fin
import           Data.Type.Length
import           Data.Type.Product hiding         (toList)
import           Data.Type.Sing
import           Data.Type.Vector                 as TCV
import           Data.Type.Vector.Util            as TCV
import           Numeric.AD
import           Prelude hiding                   (zip, map, zip3)
import           TensorOps.NatKind
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness hiding        (inner, outer)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat

konst
    :: (Tensor t, SingI n)
    => ElemT t
    -> t n
konst x = generate (\_ -> x)
{-# INLINE konst #-}

map
    :: forall k (o :: [k]) (t :: [k] -> Type). (SingI o, Tensor t)
    => (ElemT t -> ElemT t)
    -> t o
    -> t o
map f = getI . TCV.head' . liftT ((f . getI . TCV.head') :+ ØV) . (:+ ØV)
{-# INLINE map #-}

add :: (Tensor t, SingI o)
    => t o -> t o -> t o
add x y = sumT [x,y]
{-# INLINE add #-}

zipN
    :: (SingI o, Tensor t)
    => (Vec n (ElemT t) -> ElemT t)
    -> Vec n (t o)
    -> t o
zipN f = getI . TCV.head' . liftT (f :+ ØV)
{-# INLINE zipN #-}

zip :: (SingI o, Tensor t)
    => (ElemT t -> ElemT t -> ElemT t)
    -> t o
    -> t o
    -> t o
zip f x y = zipN (\case I x' :* I y' :* ØV -> f x' y') (x :+ y :+ ØV)
{-# INLINE zip #-}

zip3
    :: (SingI o, Tensor t)
    => (ElemT t -> ElemT t -> ElemT t -> ElemT t)
    -> t o
    -> t o
    -> t o
    -> t o
zip3 f x y z = zipN (\case I x' :* I y' :* I z' :* ØV -> f x' y' z') (x :+ y :+ z :+ ØV)
{-# INLINE zip3 #-}

-- | This is a huge bottleneck, I think?
--
-- Implementation issue -- shouldn't need Sing o if n or m is zero
--
gradLift
    :: forall o n m t. (Tensor t, Floating (ElemT t), SingI o)
    => Vec m (VFunc n)
    -> Vec n (t o)    -- ^ inputs
    -> Vec m (t o)    -- ^ d target / d outputs
    -> Vec n (t o)    -- ^ d target / d inputs
gradLift fs xs dtdys =
    liftT (vgen_ (\i -> I (uncurry (go i) . splitVec known)))
          (xs `TCV.append'` dtdys)
      \\ xs
  where
    go  :: Fin n
        -> Vec n (ElemT t)
        -> Vec m (ElemT t)
        -> ElemT t
    go i x dtdy = sum $ (vap . liftA2) (\d f -> d * index' i (vfGrad f x)) dtdy fs
    {-# INLINE go #-}
-- {-# INLINE[0] gradLift #-}

-- naiveGradLift
--     :: forall o n m t. (Tensor t, Floating (ElemT t), SingI o)
--     => Vec m (VFunc n)
--     -> Vec n (t o)    -- ^ inputs
--     -> Vec m (t o)    -- ^ d target / d outputs
--     -> Vec n (t o)    -- ^ d target / d inputs
-- naiveGradLift fs xs dtdys =
--     liftT (vgen_ (\i -> I (uncurry (go i) . splitVec known)))
--           (xs `TCV.append'` dtdys)
--       \\ xs
--   where
--     go  :: Fin n
--         -> Vec n (ElemT t)
--         -> Vec m (ElemT t)
--         -> ElemT t
--     go i x dtdy = sum $ (vap . liftA2) (\d (VF f) -> d * index' i (grad f x)) dtdy fs
--     {-# INLINE go #-}

-- {-# RULES
-- "gradLift/1"   gradLift = gradLift1'
-- "gradLift/1N"  gradLift = gradLift1N'
--   #-}

-- -- | 'gradLift' specialized for 'N1'.
-- gradLift1'
--     :: forall t o. (Tensor t, SingI o, Floating (ElemT t))
--     => Vec N1 (VFunc N1)
--     -> Vec N1 (t o)
--     -> Vec N1 (t o)
--     -> Vec N1 (t o)
-- gradLift1' fs xs dtdys =
--     case fs of
--       I f :* ØV -> case xs of
--         I x :* ØV -> case dtdys of
--           I dtdy :* ØV -> gradLift1 (getVF f . (:* ØV) . I) x dtdy

-- -- | 'gradLift' specialized for 'N1' -> m.
-- gradLift1N'
--     :: forall t m o. (Tensor t, SingI o, Floating (ElemT t))
--     => Vec m (VFunc N1)
--     -> Vec N1 (t o)
--     -> Vec m (t o)
--     -> Vec N1 (t o)
-- gradLift1N' fs xs dtdys =
--     case xs of
--       I x :* ØV -> gradLift1N fs x dtdys

-- -- | A faster version of 'gradLift' using forward-mode AD
-- gradLift1
--     :: forall t o. (Tensor t, SingI o, Floating (ElemT t))
--     => (forall a. Floating a => a -> a)
--     -> t o
--     -> t o
--     -> Vec N1 (t o)
-- gradLift1 f x dtdy =
--     liftT (I (\(I x' :* I d :* ØV) -> d * f x') :* ØV)
--           (I x :* I dtdy :* ØV)

-- -- | A faster version of 'gradLift' using forward-mode AD, with multiple
-- -- outputs.
-- gradLift1N
--     :: forall t m o. (Tensor t, SingI o, Floating (ElemT t))
--     => Vec m (VFunc N1)
--     -> t o
--     -> Vec m  (t o)
--     -> Vec N1 (t o)
-- gradLift1N fs x dtdys =
--     liftT (I (\(I x' :* ds) -> go x' ds) :* ØV)
--           (I x :* dtdys)
--   where
--     go  :: ElemT t
--         -> Vec m (ElemT t)
--         -> ElemT t
--     go x' dtdy = sum $ (vap . liftA2) (\d (VF f) -> d * diff (f . (:* ØV) . I) x') dtdy fs
--     {-# INLINE go #-}


inner
    :: forall t ms ns o. (Tensor t, SingI (o ': ns), SingI (ms ++ ns))
    => Length ms
    -> Length ns
    -> t (ms >: o)
    -> t (o ': ns)
    -> t (ms ++ ns)
inner lM lN x = gmul lM (LS LZ) lN x
                    \\ appendSnoc lM (Proxy @o)

outer
    :: (Tensor t, SingI ns, SingI (ms ++ ns))
    => Length ms
    -> Length ns
    -> t ms
    -> t ns
    -> t (ms ++ ns)
outer lM lN x = gmul lM LZ lN x
                    \\ appendNil lM

outerV
    :: (Tensor t, SingI '[n], SingI '[m,n])
    => t '[m]
    -> t '[n]
    -> t '[m,n]
outerV = outer (LS LZ) (LS LZ)

dot
    :: forall (t :: [k] -> Type) (m :: k). (Tensor t, SingI '[m])
    => t '[m]
    -> t '[m]
    -> t '[]
dot = inner LZ LZ

matVec
    :: (Tensor t, SingI '[n], SingI '[m])
    => t '[m, n]
    -> t '[n]
    -> t '[m]
matVec = inner (LS LZ) LZ

vecMat
    :: (Tensor t, SingI '[m,n], SingI '[n])
    => t '[m]
    -> t '[m,n]
    -> t '[n]
vecMat = inner LZ (LS LZ)

matMat
    :: (Tensor t, SingI '[n,o], SingI '[m,o])
    => t '[m,n]
    -> t '[n,o]
    -> t '[m,o]
matMat = inner (LS LZ) (LS LZ)

fromList
    :: (Tensor t, SingI ns)
    => [ElemT t]
    -> Maybe (t ns)
fromList = evalStateT . generateA $ \_ -> StateT uncons

generate
    :: forall k (t :: [k] -> Type) ns. (Tensor t, SingI ns)
    => (Prod (IndexN k) ns -> ElemT t)
    -> t ns
generate = getI . generateA . fmap I

rows
    :: (Tensor t, Applicative f, SingI (ms ++ os))
    => Length ms
    -> Length os
    -> (t ns -> f (t os))
    -> t (ms ++ ns)
    -> f (t (ms ++ os))
rows lM lO f = ixRows lM lO (\_ -> f)

toRows
    :: (Tensor t, SingI n)
    => t (n ': ns)
    -> [t ns]
toRows = ($[])
       . appEndo
       . getConst
       . rows (LS LZ) LZ (\xs -> Const $ Endo (xs:))

ixElems
    :: forall k f (t :: [k] -> Type) ns. (Applicative f, Tensor t, SingI ns)
    => (Prod (IndexN k) ns -> ElemT t -> f (ElemT t))
    -> t ns
    -> f (t ns)
ixElems f = (\\ appendNil l) $
    ixRows l LZ $ \i x ->
      konst <$> f i (unScalar (x :: t '[])) :: f (t '[])
  where
    l :: Length ns
    l = singLength sing

elems
    :: (Applicative f, Tensor t, SingI ns)
    => (ElemT t -> f (ElemT t))
    -> t ns
    -> f (t ns)
elems f = ixElems (\_ x -> f x)

itoList
    :: forall k (t :: [k] -> Type) ns. (Tensor t, SingI ns)
    => t ns
    -> [(Prod (IndexN k) ns, ElemT t)]
itoList = ($ [])
        . appEndo
        . getConst
        . ixElems (\i x -> Const $ Endo ((i,x):))

toList
    :: (Tensor t, SingI ns)
    => t ns
    -> [ElemT t]
toList = ($[])
       . appEndo
       . getConst
       . elems (\x -> Const $ Endo (x:))

unScalar
    :: forall t. Tensor t
    => t '[]
    -> ElemT t
unScalar = (! Ø)
