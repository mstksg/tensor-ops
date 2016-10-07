{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module TensorOps.NatKind where

import           Data.Finite
import           Data.Kind
import           Data.Maybe
import           Data.Singletons
import           Data.Singletons.Prelude.Num
import           Data.Type.Fin
import           Data.Type.Nat
import           Data.Type.Nat.Util
import           Data.Type.Sing
import           Type.Family.Nat
import           Type.Family.Nat.Util
import           Unsafe.Coerce
import qualified Data.Singletons.TypeLits    as GT
import qualified GHC.TypeLits                as GT

class NatKind k where
    type FromNat (n :: GT.Nat) :: k
    -- type Succ (n :: k) = (m :: k) | m -> n
    type Succ (n :: k) :: k
    type IndexN k :: k -> Type
    sFromNat :: Sing (n :: GT.Nat) -> Sing (FromNat n :: k)
    sSucc    :: Sing (n :: k) -> Sing (Succ n :: k)

instance NatKind N where
    type FromNat n = NatNat n
    type Succ n    = 'S n
    type IndexN N  = Fin
    sFromNat s = fromJust $ withNat (fromSing s) (Just . SN . unsafeCoerce)
    sSucc      = \case
      SN n -> SN (S_ n)

someNatKind
    :: NatKind k
    => Integer
    -> SomeSing k
someNatKind n = withSomeSing n (SomeSing . sFromNat)

withNatKind
    :: NatKind k
    => Integer
    -> (forall (n :: k). Sing n -> r)
    -> r
withNatKind n f = withSomeSing n (f . sFromNat)

instance NatKind GT.Nat where
    type FromNat n     = n
    type Succ n        = n GT.+ 1
    type IndexN GT.Nat = Finite
    sFromNat = id
    sSucc    = (%:+ GT.SNat @1)
