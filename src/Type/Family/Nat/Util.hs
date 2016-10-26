{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Type.Family.Nat.Util where

import           Data.Kind
import           Data.Type.Equality
import           Data.Type.Length
import           Data.Type.Nat
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.Nat
import qualified GHC.TypeLits              as GT

appendLengths
    :: Length n
    -> Length m
    -> (Len (n ++ m) :~: (Len n + Len m))
appendLengths = \case
    LZ    -> \_ -> Refl
    LS lN -> apply Refl . appendLengths lN

type family NatNat (n :: GT.Nat) = (m :: N) where
    NatNat 0 = 'Z
    NatNat n = 'S (NatNat (n GT.- 1))

data (:<=:) :: N -> N -> Type where
    LTEZ :: 'Z :<=: n
    LTES :: (m :<=: n) -> ('S m :<=: 'S n)

succAssoc
    :: forall m n. ()
    => Nat m
    -> Nat n
    -> ((m + 'S n) :~: 'S (m + n))
succAssoc = \case
    Z_   -> \_ -> Refl
    S_ m -> \n -> Refl \\ succAssoc m n

addZero
    :: Nat n
    -> ((n + 'Z) :~: n)
addZero = \case
    Z_   -> Refl
    S_ n -> Refl    \\ addZero n

