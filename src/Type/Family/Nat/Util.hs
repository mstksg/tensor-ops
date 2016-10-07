{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Type.Family.Nat.Util where

import           Data.Type.Equality
import           Data.Type.Length
import           Type.Family.List
import           Type.Family.Nat
import qualified GHC.TypeLits       as GT

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

