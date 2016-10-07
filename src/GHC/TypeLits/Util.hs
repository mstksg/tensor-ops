{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module GHC.TypeLits.Util where

import           Data.Kind
import           Data.Proxy
import           Data.Singletons
import           Data.Singletons.Prelude.Num
import           Data.Singletons.TypeLits
import           Data.Type.Equality
import           GHC.TypeLits
import           Unsafe.Coerce

data Inductive :: Nat -> Type where
    NatZ :: Inductive 0
    NatS :: KnownNat n => !(Proxy n) -> Inductive (n + 1)

inductive
    :: forall n. KnownNat n
    => Proxy n
    -> Inductive n
inductive p = case sameNat p (Proxy @0) of
    Just Refl -> NatZ
    Nothing   -> case sn %:- SNat @1 of
      SNat -> case unsafeCoerce Refl :: ((n - 1) + 1) :~: n of
        Refl -> NatS (Proxy @(n - 1))
  where
    sn :: Sing n
    sn = SNat






