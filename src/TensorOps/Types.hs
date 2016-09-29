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
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}

module TensorOps.Types where

-- import           Data.Singletons.Prelude.List hiding (Length)
-- import           Data.Type.Equality
-- import           Data.Type.Length.Util               as TCL
-- import           Data.Type.Subset
-- import           GHC.TypeLits
-- import           Unsafe.Coerce
-- import qualified Control.Foldl                       as F
import           Control.Category
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Maybe
import           Data.Singletons
import           Data.Type.Index
import           Data.Type.Length                       as TCL
import           Data.Type.Nat
import           Data.Type.Nat.Util
import           Data.Type.Product
import           Data.Type.Sing
import           Data.Type.Sing
import           Data.Type.Uniform
import           Data.Type.Vector
import           Prelude hiding                         ((.), id)
import           Statistics.Distribution
import           System.Random.MWC
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat
import           Type.Family.Nat.Util
import           Unsafe.Coerce
import qualified Data.Singletons.TypeLits               as GT
import qualified GHC.TypeLits                           as GT

class NatKind k where
    type FromNat (n :: GT.Nat) :: k
    sFromNat :: Sing (n :: GT.Nat) -> Sing (FromNat n :: k)

instance NatKind N where
    type FromNat n = NatNat n
    sFromNat s = fromJust $ withNat (fromSing s) (Just . SN . unsafeCoerce)

class Tensor (t :: [k] -> Type) where
    type ElemT t      :: Type
    type IndexT t     :: [k] -> Type

    liftT   :: (SingI o, Floating (ElemT t), Known Nat m)
            => (Vec n (ElemT t) -> Vec m (ElemT t))
            -> Vec n (t o)
            -> Vec m (t o)
    gmul    :: (SingI (ms ++ os), SingI (Reverse os ++ ns), SingI (ms ++ ns))
            => Length ms
            -> Length os
            -> Length ns
            -> t (ms         ++ os)
            -> t (Reverse os ++ ns)
            -> t (ms         ++ ns)
    transp  :: (SingI ns, SingI (Reverse ns))
            => t ns
            -> t (Reverse ns)
    -- foldT   :: (RankConstr t (n ': ns), RankConstr t ns)
    --         => F.Fold (ElemT t) (ElemT t)
    --         -> t (n ': ns)
    --         -> t ns
    -- foldTGrad :: RankConstr t (n ': ns)
    --           => (forall a. Floating a => F.Fold a a)
    --           -> t (n ': ns)
    --           -> t (n ': ns)
    diag    :: (SingI '[n], SingI ns)
            => Uniform n ns
            -> t '[n]
            -> t ns
    getDiag :: (SingI ns, SingI '[n])
            => Uniform n ns
            -> t (n ': n ': ns)
            -> t '[n]
    genRand :: (ContGen d, PrimMonad m, SingI ns)
            => d
            -> Gen (PrimState m)
            -> m (t ns)
    generateA :: (Applicative f, SingI ns)
              => (IndexT t ns -> f (ElemT t))
              -> f (t ns)
    ixElems :: Applicative f
            => ((IndexT t ns, ElemT t) -> f (ElemT t))
            -> t ns
            -> f (t ns)
    (!)     :: t ns
            -> IndexT t ns
            -> ElemT t

type TensorOp = OpPipe TOp

data TOp :: [[k]] -> [[k]] -> Type where
    -- | Lift any `R^N -> R^M` function over every element in a n-tensor list,
    -- producing a m-tensor list.
    --
    -- TODO: should be stated in Vec (Len ms) (Vec (Len ns) -> a) form, for
    -- efficiency?
    Lift    :: Uniform o ns
            -> Uniform o ms
            -> (forall a. Floating a => Vec (Len ns) a -> Vec (Len ms) a)
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

