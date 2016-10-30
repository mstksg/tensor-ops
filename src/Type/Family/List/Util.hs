{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Type.Family.List.Util where

import           Data.Proxy
import           Data.Type.Equality
import           Data.Type.Length
import           Data.Type.Nat
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.Nat
import           Unsafe.Coerce

reverseSnoc
    :: forall a as. ()
    => Length as
    -> Proxy a
    -> (Reverse (a ': as) :~: (Reverse as >: a))
reverseSnoc = \case
    LZ   -> \_ -> Refl
    LS l -> \_ -> Refl \\ reverseSnoc l (Proxy @(Head as))

snocReverse
    :: forall p a as. ()
    => Length as
    -> p a
    -> (Reverse (as >: a) :~: (a ': Reverse as))
snocReverse = \case
    LZ   -> \_ -> Refl
    LS l -> \p -> Refl \\ snocReverse l p

reverseReverse
    :: Length as
    -> (as :~: Reverse (Reverse as))
reverseReverse = \case
    LZ   -> Refl
    LS _ -> unsafeCoerce Refl

reverseConcat
    :: Length as
    -> Length bs
    -> (Reverse (as ++ bs) :~: (Reverse bs ++ Reverse as))
reverseConcat _ _ = unsafeCoerce Refl

appendNil
    :: Length ms
    -> ((ms ++ '[]) :~: ms)
appendNil = \case
    LZ   -> Refl
    LS l -> Refl \\ appendNil l

appendAssoc
    :: Length ms
    -> Length ns
    -> Length os
    -> (((ms ++ ns) ++ os) :~: (ms ++ (ns ++ os)))
appendAssoc = \case
    LZ    -> \_ _ -> Refl
    LS lM -> \lN lO -> Refl \\ appendAssoc lM lN lO

appendSnoc
    :: Length ms
    -> p n
    -> ((ms >: n) :~: (ms ++ '[n]))
appendSnoc = \case
    LZ   -> \_ -> Refl
    LS s -> \p -> Refl \\ appendSnoc s p

-- appendCons
--     :: Proxy n
--     -> Length ms
--     -> ((n ': ns) :~: ('[n] ++ ns))
-- appendCons _ _ = Refl

type family Cycle (n :: N) (as :: [k]) :: [k] where
    Cycle 'Z     xs = '[]
    Cycle ('S n) xs = xs ++ Cycle n xs

type family Replicate (n :: N) (a :: k) :: [k] where
    Replicate 'Z     x = '[]
    Replicate ('S n) x = x ': Replicate n x

-- TODO: implement and not be lazy
snocReplicate
    :: Nat n
    -> (Replicate ('S n) x :~: Replicate n x >: x)
snocReplicate _ = unsafeCoerce Refl

assocReplicate
    :: Nat n
    -> ((x ': Replicate n x) :~: (Replicate n x >: x))
assocReplicate _ = unsafeCoerce Refl

replicateLength
    :: forall x n. ()
    => Nat n
    -> Length (Replicate n x)
replicateLength = \case
    Z_   -> LZ
    S_ n -> LS (replicateLength @x n)

reverseReplicate
    :: (Replicate n xs :~: Reverse (Replicate n x))
reverseReplicate = unsafeCoerce Refl
