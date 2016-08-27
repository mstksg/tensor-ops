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
