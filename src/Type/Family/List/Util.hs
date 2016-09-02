{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Type.Family.List.Util where

import           Data.Proxy
import           Data.Type.Equality
import           Data.Type.Length
import           Type.Class.Witness
import           Type.Family.List
import           Unsafe.Coerce

reverseSnoc
    :: forall a as. ()
    => Length as
    -> Proxy a
    -> (Reverse (a ': as) :~: (Reverse as >: a))
reverseSnoc = \case
    LZ   -> \_ -> Refl
    LS l -> \_ -> Refl \\ reverseSnoc l (Proxy @(Head as))

snocReverse
    :: forall a as. ()
    => Length as
    -> Proxy a
    -> (Reverse (as >: a) :~: (a ': Reverse as))
snocReverse = \case
    LZ   -> \_ -> Refl
    LS l -> \p -> Refl \\ snocReverse l p

reverseReverse
    :: Length as
    -> (as :~: Reverse (Reverse as))
reverseReverse = \case
    LZ   -> Refl
    LS _ -> undefined

reverseConcat
    :: Length as
    -> Length bs
    -> (Reverse (as ++ bs) :~: (Reverse bs ++ Reverse as))
reverseConcat _ _ = unsafeCoerce Refl

appendNil
    :: Length ms
    -> ((ms ++ '[]) :~: ms)
appendNil = \case
    LZ   -> Refl
    LS l -> Refl \\ appendNil l

appendAssoc
    :: Length ms
    -> Length ns
    -> Length os
    -> (((ms ++ ns) ++ os) :~: (ms ++ (ns ++ os)))
appendAssoc = \case
    LZ    -> \_ _ -> Refl
    LS lM -> \lN lO -> Refl \\ appendAssoc lM lN lO

appendSnoc
    :: Length ms
    -> Proxy n
    -> ((ms >: n) :~: (ms ++ '[n]))
appendSnoc = \case
    LZ   -> \_ -> Refl
    LS s -> \p -> Refl \\ appendSnoc s p

-- appendCons
--     :: Proxy n
--     -> Length ms
--     -> ((n ': ns) :~: ('[n] ++ ns))
-- appendCons _ _ = Refl
