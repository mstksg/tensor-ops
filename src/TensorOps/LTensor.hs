{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module TensorOps.LTensor where

import           Control.Applicative
import           Data.Kind
import           Data.Type.Combinator
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Product
import           Data.Type.Product.Util as TCP
import           Data.Type.Uniform
import           Data.Type.Vector       as TCV
import           Data.Type.Vector.Util
import           TensorOps.Tensor
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.Nat

data NestedVec :: [N] -> Type -> Type where
    NVZ :: !a -> NestedVec '[]  a
    NVS :: VecT n (NestedVec ns) a -> NestedVec (n ': ns) a

deriving instance Functor (NestedVec ns)
instance Known (Prod Nat) ns => Applicative (NestedVec ns) where
    pure x = case known :: Length ns of
               LZ   -> NVZ x
               LS l -> NVS $ vgen_ (\_ -> pure x)
    (<*>) = \case
      NVZ f -> \case
        NVZ x -> NVZ (f x)
      NVS fs -> \case
        NVS xs -> NVS $ vap (<*>) fs xs

newtype LTensor :: [N] -> Type where
    LTensor :: { getNVec :: NestedVec ns Double
               } -> LTensor ns

instance Tensor LTensor where
    type ElemT LTensor = Double

    -- liftT :: forall o ns ms. ()
    --       => Uniform o ns
    --       -> Uniform o ms
    --       -> (Vec (Len ns) Double -> Vec (Len ms) Double)
    --       -> Prod LTensor ns
    --       -> Prod LTensor ms
    -- liftT uN uM f xs = undefined
    --   where
    --     xsV :: Vec (Len ns) (NestedVec o Double)
    --     xsV = prodToVec (I . getNVec) uN xs
    --     ysV :: NestedVec o (Vec (Len ms) Double)
    --     ysV = liftVec f xsV \\ uniformLength uM
    --   -- where
    --   --   go  :: (Vec (Len ns) Double -> Vec (Len ms) Double)
    --   --       -> Uniform o ms
    --   --       -> Uniform o ns
    --   --       -> Prod LTensor ns
    --   --       -> Prod LTensor ms
    --   --   go f uM uN xs = undefined
    --   --     where
    --   --       xsV = prodToVec (I . getNVec) uN xs
    --       -- UØ    -> \_ _ -> Ø
    --       -- US uM -> \case
    --       --   UØ -> \case
    --           -- Ø -> case f ØV of
    --           --        ys -> vecToProd (\(I y) -> konst y) (US uM) ys
    --       --   US uN -> \case
    --       --     x :< xs -> case fmap (_ . f . _) x of
    --                        -- _ -> _
    --           -- go (f . _) (US uM) uN xs


    -- liftT uN uM f = \case
    --   Ø -> case uM of
    --          UØ     -> Ø
    --          US uM' -> case f ØV of
    --                      I y :* ys -> konst y :< liftT uN uM' (\_ -> ys) Ø
    --   I x :< xs case uM of

