{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE StandaloneDeriving      #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}

module TensorOps.Types where

import           Control.Category
import           Control.Monad.Primitive
import           Data.Finite
import           Data.Kind
import           Data.Singletons
import           Data.Type.Index
import           Data.Type.Length        as TCL
import           Data.Type.Product
import           Data.Type.Sing
import           Data.Type.Uniform
import           Data.Type.Vector
import           Prelude hiding          ((.), id)
import           Statistics.Distribution
import           System.Random.MWC
import           TensorOps.NatKind
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat


class NatKind k => Tensor (t :: [k] -> Type) where
    type ElemT t  :: Type
    -- type IndexT t :: [k] -> Type
    -- type IndexT (t :: [k] -> Type) = Prod (IndexN k)

    -- TODO: can we detach Vec from liftT ?
    liftT   :: SingI o
            -- => (Vec n (ElemT t) -> Vec m (ElemT t))
            => Vec m (Vec n (ElemT t) -> ElemT t)
            -> Vec n (t o)
            -> Vec m (t o)
    gmul    :: (SingI (Reverse os ++ ns), SingI (ms ++ ns))
            => Length ms
            -> Length os
            -> Length ns
            -> t (ms         ++ os)
            -> t (Reverse os ++ ns)
            -> t (ms         ++ ns)
    transp  :: (SingI ns, SingI (Reverse ns))
            => t ns
            -> t (Reverse ns)
    diag    :: SingI ns
            => Uniform n ns
            -> t '[n]
            -> t ns
    getDiag :: SingI n
            => Uniform n ns
            -> t (n ': n ': ns)
            -> t '[n]
    genRand :: (ContGen d, PrimMonad m, SingI ns)
            => d
            -> Gen (PrimState m)
            -> m (t ns)
    generateA :: (Applicative f, SingI ns)
              => (Prod (IndexN k) ns -> f (ElemT t))
              -> f (t ns)
    ixRows
        :: (Applicative f, SingI (ms ++ os))
        => Length ms
        -> Length os
        -> (Prod (IndexN k) ms -> t ns -> f (t os))
        -> t (ms ++ ns)
        -> f (t (ms ++ os))
    (!) :: t ns
        -> Prod (IndexN k) ns
        -> ElemT t

type TensorOp = OpPipe TOp

-- | A kludge to get around lack of impredicative types in Haskell
newtype VFunc n = VF { getVF :: forall a. Floating a => Vec n a -> a }

data TOp :: [[k]] -> [[k]] -> Type where
    -- | Lift any `R^N -> R^M` function over every element in a n-tensor list,
    -- producing a m-tensor list.
    Lift    :: Uniform o ns
            -> Uniform o ms
            -- -> (forall a. Floating a => Vec (Len ns) a -> Vec (Len ms) a)
            -- -> (forall a. Floating a => Vec (Len ms) (Vec (Len ns) a -> a))
            -> Vec (Len ms) (VFunc (Len ns))
            -> TOp ns ms
    -- | Generalized tensor product
    GMul    :: Length ms
            -> Length os
            -> Length ns
            -> TOp '[ (ms ++ os), (Reverse os ++ ns) ] '[ ms ++ ns ]
    -- | Transpose (reverse indices)
    --
    -- TODO: allow for arbitrary permutation
    Transp  :: Length ns
            -> TOp '[ns] '[Reverse ns]
    -- -- | Fold along the principle direction
    -- Fold    :: Length ns
    --         -> (forall a. Floating a => F.Fold a a)
    --         -> TOp '[n ': ns] '[ns]
    -- should this also include indices to go backwards?  how can this be
    -- statically verified?
    Shuffle :: Prod (Index ns) ms
            -> TOp ns ms

-- | TODO: replace with `syntactic`?
data OpPipe :: ([k] -> [k] -> Type) -> [k] -> [k] -> Type where
    OPØ   :: OpPipe f a a
    Pop   :: Sing a
          -> Sing b
          -> Sing d
          -> f a b
          -> OpPipe f (b ++ d) c
          -> OpPipe f (a ++ d) c

pappend
    :: forall a b c d f. ()
    => Sing a
    -> Sing b
    -> Sing d
    -> OpPipe f a b
    -> OpPipe f (b ++ d) c
    -> OpPipe f (a ++ d) c
pappend _ sB sD = \case
    OPØ -> id
    Pop (sA' :: Sing a')
        (sB' :: Sing b')
        (sD' :: Sing d')
        (x   :: f a' b'  )
        (xs  :: OpPipe f (b' ++ d') b)
          -> \ys -> let lD' :: Length d'
                        lD' = singLength sD'
                    in  Pop sA' sB' (sD' %:++ sD) x (pappend (sB' %:++ sD') sB sD xs ys)
                          \\ appendAssoc (singLength sA') lD' lD
                          \\ appendAssoc (singLength sB') lD' lD
  where
    lD :: Length d
    lD = singLength sD


pop :: forall a b c d f. (SingI a, SingI b, SingI d)
    => Length d
    -> f a b
    -> OpPipe f (b ++ d) c
    -> OpPipe f (a ++ d) c
pop _ = Pop (sing :: Sing a) (sing :: Sing b) (sing :: Sing d)

infixr 4 ~.
(~.)
    :: (SingI a, SingI b, SingI d)
    => (Length a, Length d, f a b)
    -> OpPipe f (b ++ d) c
    -> OpPipe f (a ++ d) c
(_, lD, x) ~. y = pop lD x y

instance Eq1 Finite
