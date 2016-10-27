{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE InstanceSigs            #-}
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
{-# LANGUAGE ViewPatterns            #-}

module TensorOps.Types where

import           Control.Category
import           Control.Monad.Primitive
import           Data.Finite
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude hiding (Reverse, (%:++))
import           Data.Type.Combinator
import           Data.Type.Length               as TCL
import           Data.Type.Product              as TCP
import           Data.Type.Product.Util         as TCP
import           Data.Type.Sing
import           Data.Type.Uniform
import           Data.Type.Vector
import           Prelude hiding                 ((.), id)
import           Statistics.Distribution
import           System.Random.MWC
import           TensorOps.NatKind
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util

{-# RULES
"realToFrac/Double->Double" realToFrac = id :: Double -> Double
"realToFrac/Float->Float" realToFrac = id :: Float -> Float
    #-}

class NatKind k => Tensor (t :: [k] -> Type) where
    type ElemT t  :: Type

    -- TODO: can we detach Vec from liftT ?
    liftT   :: SingI o
            => (Vec n (ElemT t) -> ElemT t)
            -> Vec n (t o)
            -> t o
    gmul    :: (SingI (Reverse os ++ ns), SingI (ms ++ ns))
            => Length ms
            -> Length os
            -> Length ns
            -> t (ms         ++ os)
            -> t (Reverse os ++ ns)
            -> t (ms         ++ ns)
    -- is a list really the best data structure here?
    -- maybe Foldable f?
    sumT    :: SingI o => [t o] -> t o
    scaleT  :: SingI o => ElemT t -> t o -> t o
    transp  :: (SingI ns, SingI (Reverse ns))
            => t ns
            -> t (Reverse ns)
    -- sumRow  :: Remove ns n ms
    --         -> t ns
    --         -> t ms
    mapRows :: SingI (ns ++ ms)
            => Length ns
            -> (t ms -> t ms)
            -> t (ns ++ ms)
            -> t (ns ++ ms)
    sumRows :: (SingI (n ': ns), SingI ns)
            => t (n ': ns)
            -> t ns
    diag    :: SingI (n ': ns)
            => Uniform n ns
            -> t '[n]
            -> t (n ': ns)
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

-- type TensorOp = OpPipe TOp

-- | Function and gradient
data VFunc n
    = VF { vfFunc :: !(forall a. RealFloat a => Vec n a -> a      )
         , vfGrad :: !(forall a. RealFloat a => Vec n a -> Vec n a)
         }

-- -- | A kludge to get around lack of impredicative types in Haskell
-- newtype VFunc n = VF { getVF :: forall a. RealFloat a => Vec n a -> a }

data TOp :: [[k]] -> [[k]] -> Type where
    TOp :: { runTOp   :: !(forall t. (Tensor t, RealFloat (ElemT t)) => Prod t ns -> Prod t ms)
           , gradTOp' :: !(forall t. (Tensor t, RealFloat (ElemT t)) => Prod t ns -> Prod t ms -> Prod t ns)
           } -> TOp ns ms

gradTOp
    :: (Tensor t, RealFloat (ElemT t))
    => TOp ns '[ '[] ]
    -> Prod t ns
    -> Prod t ns
gradTOp o xs = gradTOp' o xs (only (getI $ generateA (\_ -> I 1)))


instance Category TOp where
    id = TOp id
             (flip const)

    (.) :: forall as bs cs. ()
        => TOp bs cs
        -> TOp as bs
        -> TOp as cs
    TOp f2 g2 . TOp f1 g1 = TOp f3 g3
      where
        f3  :: forall t. (Tensor t, RealFloat (ElemT t))
            => Prod t as
            -> Prod t cs
        f3 = f2 . f1
        g3  :: forall t. (Tensor t, RealFloat (ElemT t))
            => Prod t as
            -> Prod t cs
            -> Prod t as
        g3 xs ds = g1 xs ds'
          where
            ys :: Prod t bs
            ys  = f1 xs
            ds' :: Prod t bs
            ds' = g2 ys ds

idOp
    :: forall ns. ()
    => TOp ns ns
idOp = id

(*>>)
    :: forall as bs cs ds. (Known Length as, Known Length bs)
    => TOp as bs
    -> TOp (bs ++ cs) ds
    -> TOp (as ++ cs) ds
t1 *>> t2 = (t1 *** idOp @cs) >>> t2
infixr 0 *>>

(<<*)
    :: forall as bs cs ds. (Known Length as, Known Length bs)
    => TOp (bs ++ cs) ds
    -> TOp as bs
    -> TOp (as ++ cs) ds
(<<*) = flip ((*>>) @as @bs @cs @ds)
infixr 2 <<*

(***)
    :: forall as bs cs ds. (Known Length as, Known Length cs)
    => TOp as cs
    -> TOp bs ds
    -> TOp (as ++ bs) (cs ++ ds)
TOp f1 g1 *** TOp f2 g2 = TOp f3 g3
  where
    f3  :: forall t. (Tensor t, RealFloat (ElemT t))
        => Prod t (as ++ bs)
        -> Prod t (cs ++ ds)
    f3 = overProdSplit known f1 f2
    g3  :: forall t. (Tensor t, RealFloat (ElemT t))
        => Prod t (as ++ bs)
        -> Prod t (cs ++ ds)
        -> Prod t (as ++ bs)
    g3 (splitProd known->(xs, ys)) = overProdSplit known (g1 xs) (g2 ys)

(&&&)
    :: forall as bs cs. (Known Length bs, SingI as)
    => TOp as bs
    -> TOp as cs
    -> TOp as (bs ++ cs)
TOp f1 g1 &&& TOp f2 g2 = TOp f3 g3
  where
    f3  :: forall t. (Tensor t, RealFloat (ElemT t))
        => Prod t as
        -> Prod t (bs ++ cs)
    f3 = TCP.append' <$> f1 <*> f2
    g3  :: forall t. (Tensor t, RealFloat (ElemT t))
        => Prod t as
        -> Prod t (bs ++ cs)
        -> Prod t as
    g3 xs (splitProd known->(dtdys,dtdzs)) =
        zipProdWith3 (\s gxy gxz -> sumT [gxy,gxz] \\ s)
                     (singProd sing)
                     (g1 xs dtdys)
                     (g2 xs dtdzs)


-- -- | TODO: replace with `syntactic`?
-- data OpPipe :: ([k] -> [k] -> Type) -> [k] -> [k] -> Type where
--     OPØ   :: OpPipe f a a
--     Pop   :: !(Sing a)
--           -> !(Sing b)
--           -> !(Sing d)
--           -> !(f a b)
--           -> !(OpPipe f (b ++ d) c)
--           -> OpPipe f (a ++ d) c

-- pappend
--     :: forall a b c d f. ()
--     => Sing a
--     -> Sing b
--     -> Sing d
--     -> OpPipe f a b
--     -> OpPipe f (b ++ d) c
--     -> OpPipe f (a ++ d) c
-- pappend _ sB sD = \case
--     OPØ -> id
--     Pop (sA' :: Sing a')
--         (sB' :: Sing b')
--         (sD' :: Sing d')
--         (x   :: f a' b'  )
--         (xs  :: OpPipe f (b' ++ d') b)
--           -> \ys -> let lD' :: Length d'
--                         lD' = singLength sD'
--                     in  Pop sA' sB' (sD' %:++ sD) x (pappend (sB' %:++ sD') sB sD xs ys)
--                           \\ appendAssoc (singLength sA') lD' lD
--                           \\ appendAssoc (singLength sB') lD' lD
--   where
--     lD :: Length d
--     lD = singLength sD

-- pipe
--     :: forall t a b. (SingI a, SingI b)
--     => t a b
--     -> OpPipe t a b
-- pipe o = Pop sing sing SNil o OPØ
--            \\ appendNil (singLength (sing :: Sing a))
--            \\ appendNil (singLength (sing :: Sing b))

-- pop :: forall a b c d f. (SingI a, SingI b, SingI d)
--     => Length d
--     -> f a b
--     -> OpPipe f (b ++ d) c
--     -> OpPipe f (a ++ d) c
-- pop _ = Pop (sing :: Sing a) (sing :: Sing b) (sing :: Sing d)

-- infixr 4 ~.
-- (~.)
--     :: (SingI a, SingI b, SingI d)
--     => (Length a, Length d, f a b)
--     -> OpPipe f (b ++ d) c
--     -> OpPipe f (a ++ d) c
-- (_, lD, x) ~. y = pop lD x y

instance Eq1 Finite
