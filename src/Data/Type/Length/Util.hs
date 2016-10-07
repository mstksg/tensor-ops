{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Length.Util where

import           Data.Kind
import           Data.Proxy
import           Data.Type.Length
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Unsafe.Coerce

append'
    :: Length ns
    -> Length ms
    -> Length (ns ++ ms)
append' = \case
    LZ   -> id
    LS l -> LS . append' l

-- TODO: could PROBABLY just be unsafeCoerce?
-- also, make the product reverse' efficient.
reverse'
    :: forall ns. ()
    => Length ns
    -> Length (Reverse ns)
reverse' = unsafeCoerce
-- reverse' = \case
--     LZ   -> LZ
--     LS l -> reverse' l >: (Proxy @(Head ns))

(>:)
    :: Length ns
    -> Proxy n
    -> Length (ns >: n)
(>:) = \case
    LZ   -> \_ -> LS LZ
    LS l -> LS . (l >:)

data SnocLength :: [a] -> Type where
    SnocZ :: SnocLength '[]
    SnocS :: SnocLength as -> Proxy a -> SnocLength (as >: a)

snocLengthHelp
    :: forall as bs. ()
    => Length bs
    -> SnocLength bs
    -> Length as
    -> SnocLength (bs ++ as)
snocLengthHelp lB sB = \case
    LZ                            ->
        sB      \\ appendNil lB
    lA@(LS lA') ->
        snocLengthHelp (lB >: p lA) (SnocS sB (p lA)) lA'
                \\ appendSnoc lB (p lA)
                \\ appendAssoc lB (l lA) lA'
  where
    p :: forall c cs. Length (c ': cs) -> Proxy c
    p _ = Proxy
    l :: forall c cs. Length (c ': cs) -> Length '[c]
    l _ = LS LZ

-- | could this be unsafeCoerce?
snocLength
    :: Length as
    -> SnocLength as
snocLength l = snocLengthHelp LZ SnocZ l

-- | could just be unsafeCoerce lol
snocLengthLength
    :: SnocLength as
    -> Length as
snocLengthLength = \case
    SnocZ     -> LZ
    SnocS l s -> snocLengthLength l >: s

snocLengthReverse
    :: SnocLength as
    -> Length (Reverse as)
snocLengthReverse = \case
    SnocZ     -> LZ
    SnocS (s :: SnocLength bs) (p :: Proxy b) ->
      LS (snocLengthReverse s)
        \\ snocReverse (snocLengthLength s) p

