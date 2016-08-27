{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Length.Util where

import           Data.Proxy
import           Data.Type.Equality
import           Data.Type.Length
import           Type.Class.Witness
import           Type.Family.List

append'
    :: Length ns
    -> Length ms
    -> Length (ns ++ ms)
append' = \case
    LZ   -> id
    LS l -> LS . append' l

reverse'
    :: forall ns. ()
    => Length ns
    -> Length (Reverse ns)
reverse' = \case
    LZ -> LZ
    LS l -> reverse' l >: (Proxy @(Head ns))

(>:)
    :: Length ns
    -> Proxy n
    -> Length (ns >: n)
(>:) = \case
    LZ   -> \_ -> LS LZ
    LS l -> LS . (l >:)

