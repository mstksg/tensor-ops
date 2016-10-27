{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module TensorOps.Learn.NeuralNet.Recurrent where

import           Data.Kind
import           Data.Singletons
import           Data.Type.Index
import           Data.Type.Length      as TCL
import           Data.Type.Length.Util as TCL
import           Data.Type.Product     as TCP
import           Data.Type.Sing
import           TensorOps.Types
import           Type.Class.Known
import           Type.Class.Witness
import           Data.Singletons.Prelude hiding ((%:++))
import           Type.Family.List
import           Type.Family.List.Util

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { _nsSs    :: !(Sing ss)
         , _nsOs    :: !(Sing os)
         , _nOp     :: !(TensorOp ('[i] ': ss ++ os) ('[o] ': ss))
         , _nState  :: !(Prod t ss)
         , _nParams :: !(Prod t os)
         } -> Network t i o

(~*~)
    :: forall k (t :: [k] -> Type) a b c. (SingI a, SingI c, SingI b)
    => Network t a b
    -> Network t b c
    -> Network t a c
(~*~) = \case
  N (sSs1 :: Sing ss1)
    (sOs1 :: Sing os1)
    (o1   :: TensorOp ('[a] ': ss1 ++ os1) ('[b] ': ss1))
    (s1   :: Prod t ss1)
    (p1   :: Prod t os1) -> \case
    N (sSs2 :: Sing ss2)
      (sOs2 :: Sing os2)
      (o2   :: TensorOp ('[b] ': ss2 ++ os2) ('[c] ': ss2))
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
          shuffle1
              :: TOp ('[a] ': (ss2 ++ ss1) ++ os1)
                     ('[a] ': (ss1 ++ os1) ++ ss2)
          shuffle1 = undefined
          apO1
              :: TensorOp ('[a] ': (ss1 ++ os1) ++ ss2)
                          ('[b] ': ss1 ++ ss2)
          apO1 = pappend (sing `SCons` sSs1 %:++ sOs1) (sing `SCons` sSs1) sSs2 o1 OPØ
          shuffleApO1
              :: TensorOp ('[a] ': (ss2 ++ ss1) ++ os1)
                          ('[b] ': ss1 ++ ss2)
          shuffleApO1 = ( LS @[k] @_ @'[a] (lSs2 `TCL.append'` lSs1 `TCL.append'` lOs1)
                        , LZ
                        , shuffle1
                        )
                     ~. apO1
                          \\ appendNil (lSs2 `TCL.append'` lSs1 `TCL.append'` lOs1)
                          \\ appendNil (lSs1 `TCL.append'` lOs1 `TCL.append'` lSs2)
                          \\ (sSs1 %:++ sOs1) %:++ sSs2
                          \\ (sSs2 %:++ sSs1) %:++ sOs1
          shuffle2
              :: TOp ('[b] ': (ss1 ++ ss2) ++ os2)
                     ('[b] ': (ss2 ++ os2) ++ ss1)
          shuffle2 = undefined
          apO2
              :: TensorOp ('[b] ': (ss2 ++ os2) ++ ss1)
                          ('[c] ': ss2 ++ ss1)
          apO2 = pappend (sing `SCons` sSs2 %:++ sOs2) (sing `SCons` sSs2) sSs1 o2 OPØ
          shuffleApO2
              :: TensorOp ('[b] ': (ss1 ++ ss2) ++ os2)
                          ('[c] ': ss2 ++ ss1)
          shuffleApO2 = ( LS @[k] @_ @'[b] (lSs1 `TCL.append'` (lSs2 `TCL.append'` lOs2))
                        , LZ
                        , shuffle2
                        )
                     ~. apO2
                          \\ appendNil (lSs2 `TCL.append'` lOs2 `TCL.append'` lSs1)
                          \\ appendNil (lSs1 `TCL.append'` (lSs2 `TCL.append'` lOs2))
                          \\ appendAssoc lSs1 lSs2 lOs2
                          \\ (sSs1 %:++ sSs2) %:++ sOs2
                          \\ (sSs2 %:++ sOs2) %:++ sSs1
          o :: TensorOp ('[a] ': (ss2 ++ ss1) ++ (os1 ++ os2)) ('[c] ': ss2 ++ ss1)
          o = pappend (sing `SCons` sSs2 %:++ sSs1 %:++ sOs1)
                      (sing `SCons` sSs1 %:++ sSs2)
                      sOs2
                      shuffleApO1
                      shuffleApO2
                \\ appendAssoc lSs1 lOs1 lOs2
                \\ appendAssoc lSs2 lSs1 lOs1
                \\ (undefined :: ((ss2 ++ (ss1 ++ os1)) ++ os2) :~: ((ss2 ++ ss1) ++ (os1 ++ os2)))
      in N (sSs2 %:++ sSs1)
           (sOs1 %:++ sOs2)
           o
           (s2 `TCP.append'` s1)
           (p1 `TCP.append'` p2)
infixr 4 ~*~

