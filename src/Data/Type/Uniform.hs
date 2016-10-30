{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Type.Uniform where

import           Data.Kind
import           Data.Type.Length
import           Type.Class.Known
import           Type.Class.Witness
import           Data.Type.Nat
import           Type.Family.List.Util
import           Type.Family.Constraint
import           Type.Family.List

-- | A @'Uniform' a as@ is a witness that every item in @as@ is
-- (identically) @a@.
data Uniform :: a -> [a] -> Type where
    UØ :: Uniform a '[]
    US :: !(Uniform a as) -> Uniform a (a ': as)

deriving instance Show (Uniform a as)

uniformLength :: Uniform n ns -> Length ns
uniformLength = \case
    UØ   -> LZ
    US u -> LS (uniformLength u)

instance Known (Uniform n) '[] where
    known = UØ

instance Known (Uniform n) ns => Known (Uniform n) (n ': ns) where
    known = US known

-- instance (m ~ Len ns) => Witness ØC (Known Nat m) (Uniform n ns) where
--     (\\) r = \case
--       UØ   -> r
--       US u -> r \\ u

instance Witness ØC (Known Length ms) (Uniform m ms) where
    (\\) r = \case
      UØ   -> r
      US u -> r \\ u

appendUniform
    :: Uniform o ns
    -> Uniform o ms
    -> Uniform o (ns ++ ms)
appendUniform = \case
    UØ   -> id
    US u -> US . appendUniform u

replicateUniform
    :: forall x n. ()
    => Nat n
    -> Uniform x (Replicate n x)
replicateUniform = \case
    Z_   -> UØ
    S_ n -> US (replicateUniform @x n)

