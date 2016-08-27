{-# LANGUAGE GADTs         #-}
{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Type.Family.Nat.Util where

-- import           Data.Singletons.Prelude.List ((:++))
import           Data.Type.Equality
import           Type.Family.List
import           Data.Type.Length
import           Type.Family.Nat

appendLengths
    :: Length n
    -> Length m
    -> (Len (n ++ m) :~: (Len n + Len m))
appendLengths = \case
    LZ    -> \_ -> Refl
    LS lN -> apply Refl . appendLengths lN
