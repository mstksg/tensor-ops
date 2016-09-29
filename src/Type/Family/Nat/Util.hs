{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Type.Family.Nat.Util where

-- import           Data.Singletons.Prelude.List ((:++))
import           Data.Proxy
import           Data.Singletons.Prelude.Num
import           Data.Type.Equality
import           Data.Type.Length
import           Type.Family.List
import           Type.Family.Nat
import qualified GHC.TypeLits                    as GT

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

-- instance PNum ('Proxy :: Proxy N) where
--     type x :+ y = x + y
--     type x :* y = x * y
--     type Signum x = N1
--     type FromInteger x = NatNat x


-- type family (x :: N) - (y :: N) where

