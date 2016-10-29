{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Learn.NeuralNet.Recurrent where

import           Control.Category hiding        ((.), id)
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude hiding ((%:++))
import           Data.Type.Index
import           Data.Type.Length               as TCL
import           Data.Type.Length.Util          as TCL
import           Data.Type.Product              as TCP
import           Data.Type.Product.Util         as TCP
import           Data.Type.Sing
import           TensorOps.TOp                  as TO
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import           Type.Family.List.Util
import           Unsafe.Coerce

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { _nsSs    :: !(Sing ss)
         , _nsOs    :: !(Sing os)
         , _nOp     :: !(TOp ('[i] ': ss ++ os) ('[o] ': ss))
         , _nState  :: !(Prod t ss)
         , _nParams :: !(Prod t os)
         } -> Network t i o

(~*~)
    :: forall k (t :: [k] -> Type) a b c. ()
    => Network t a b
    -> Network t b c
    -> Network t a c
(~*~) = \case
  N (sSs1 :: Sing ss1)
    (sOs1 :: Sing os1)
    (o1   :: TOp ('[a] ': ss1 ++ os1) ('[b] ': ss1))
    (s1   :: Prod t ss1)
    (p1   :: Prod t os1) -> \case
    N (sSs2 :: Sing ss2)
      (sOs2 :: Sing os2)
      (o2   :: TOp ('[b] ': ss2 ++ os2) ('[c] ': ss2))
      (s2   :: Prod t ss2)
      (p2   :: Prod t os2) ->
      let lSs1 :: Length ss1
          lSs1 = singLength sSs1
          lSs2 :: Length ss2
          lSs2 = singLength sSs2
          lOs1 :: Length os1
          lOs1 = singLength sOs1
          lOs2 :: Length os2
          lOs2 = singLength sOs2
          o :: TOp ('[a] ': (ss2 ++ ss1) ++ (os1 ++ os2)) ('[c] ': ss2 ++ ss1)
                    -- all these proofs lol
          o     = (\\ (unsafeCoerce Refl :: ((ss2 ++ ss1) ++ os1) ++ os2 :~: (ss2 ++ ss1) ++ (os1 ++ os2))) $
                  (\\ (unsafeCoerce Refl :: ((ss1 ++ os1) ++ ss2) ++ os2 :~: (ss1 ++ os1) ++ (ss2 ++ os2))) $
                  (\\ appendAssoc lSs1 lSs2 lOs2                  ) $
                  (\\ appendAssoc lSs2 lSs1 lOs1                  ) $
                  (\\ (lSs2 `TCL.append'` lSs1) `TCL.append'` lOs1) $
                  (\\ (lSs1 `TCL.append'` lOs1) `TCL.append'` lSs2) $
                  (\\ lSs1                                        ) $
                  (\\ lSs2                                        ) $
                  (\\ lSs1 `TCL.append'` lOs1                     ) $
                  (\\ lSs2 `TCL.append'` lOs2                     ) $
                    secondOp @'[ '[a] ]
                      (firstOp @os2 (TO.swap' lSs2 (lSs1 `TCL.append'` lOs1))
                      )
                >>> firstOp @(ss2 ++ os2) o1
                >>> secondOp @'[ '[b] ] (TO.swap' lSs1 (lSs2 `TCL.append'` lOs2))
                >>> firstOp @ss1 o2
      in  N (sSs2 %:++ sSs1)
            (sOs1 %:++ sOs2)
            o
            (s2 `TCP.append'` s1)
            (p1 `TCP.append'` p2)
infixr 4 ~*~

runNetwork
    :: (RealFloat (ElemT t), Tensor t)
    => t '[i]
    -> Network t i o
    -> (t '[o], Network t i o)
runNetwork x (N sS sO o s p) =
        (\case y :< s' -> (y, N sS sO o s' p))
      . runTOp o
      $ x :< (s `TCP.append'` p)

