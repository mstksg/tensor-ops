{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE EmptyCase      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Data.Type.Remove.Util where

import           Data.Kind
import           Data.Proxy
import           Data.Type.Length
import           Data.Type.Remove
import           Type.Family.List

data RemPart :: [k] -> k -> [k] -> Type where
    RP  :: !(Length cs)
        -> !(Proxy a)
        -> !(Length ds)
        -> RemPart (cs ++ '[a] ++ ds) a (cs ++ ds)

remPart :: Length as -> Remove as a bs -> RemPart as a bs
remPart = \case
    LZ   -> \case
    LS l -> \case
      RZ   -> RP LZ Proxy l
      RS s -> case remPart l s of
                RP lC pA lD -> RP (LS lC) pA lD

