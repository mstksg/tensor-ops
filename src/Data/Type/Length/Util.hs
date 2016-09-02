{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Length.Util where

import           Data.Kind
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

data ViewR :: [k] -> Type where
    RNil  :: ViewR '[]
    RSnoc :: Proxy n -> Length ns -> ViewR (ns >: n)


viewR
    :: Length ns
    -> ViewR ns
viewR = \case
    LZ   -> RNil
    LS l -> case viewR l of
              RNil       -> RSnoc Proxy LZ
              RSnoc p l' -> RSnoc p (LS l')
