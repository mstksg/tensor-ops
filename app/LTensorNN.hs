{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-- import           Data.Type.Nat.Quote
-- import           GHC.TypeLits
-- import           Statistics.Distribution
import           Control.Category
import           Control.Monad
import           Control.Monad.Primitive
import           Data.Kind
import           Data.List hiding                ((\\))
import           Data.Maybe
import           Data.Singletons
import           Data.Singletons.Prelude.List    (Sing(..))
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Product               as TCP
import           Data.Type.Product.Util
import           Data.Type.Sing
import           Data.Type.Uniform
import           Prelude hiding                  ((.), id)
import           Statistics.Distribution.Normal
import           Statistics.Distribution.Uniform
import           System.Random.MWC
import           TensorOps.Gradient
import           TensorOps.LTensor
import           TensorOps.Run
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Higher.Util
import           Type.Class.Known
import           Type.Class.Witness hiding       (inner)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.Family.Nat
import qualified TensorOps.TOp                   as TO
import qualified TensorOps.Tensor                as TT


ffLayer'
    :: (SingI i, SingI o)
    => TensorOp '[ '[i], '[o,i], '[o]] '[ '[o] ]
ffLayer' = (LS (LS LZ), LS LZ, TO.flip                   )
        ~. (LS (LS LZ), LS LZ, GMul    (LS LZ) (LS LZ) LZ)
        ~. (LS (LS LZ), LZ   , TO.zip2 (+)               )
        ~. (LS LZ     , LZ   , TO.map  (US UØ) logistic  )
        ~. OPØ

logistic
    :: forall a. Floating a
    => a
    -> a
logistic x = 1 / (1 + exp (- x))

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { nsOs     :: Sing os
         , nOp      :: TensorOp ('[i] ': os) '[ '[o] ]
         , nParams  :: Prod t os
         } -> Network t i o

(~**)
    :: (SingI a, SingI b)
    => Network t a b
    -> Network t b c
    -> Network t a c
N sOs1 o1 p1 ~** N sOs2 o2 p2 =
    N (sOs1 %:++ sOs2)
      (pappend (sing `SCons` sOs1) sing sOs2 o1 o2)
      (p1 `TCP.append'` p2)

ffLayer
    :: forall i o m t. (SingI i, SingI o, PrimMonad m, Tensor t)
    => Gen (PrimState m)
    -> m (Network t i o)
ffLayer g = (\w b -> N sing ffLayer' (w :< b :< Ø))
        <$> genRand (normalDistr 0 0.5) g
        <*> genRand (normalDistr 0 0.5) g

genNet
    :: forall k o i m (t :: [k] -> Type). (SingI o, SingI i, PrimMonad m, Tensor t)
    => [SomeSing k]
    -> Gen (PrimState m)
    -> m (Network t i o)
genNet xs0 g = go sing xs0
  where
    go  :: forall j. ()
        => Sing j
        -> [SomeSing k]
        -> m (Network t j o)
    go sj = \case
      []   -> ffLayer g           \\ sj
      x:xs -> case x of
        SomeSing sl -> do
          n <- go sl xs
          l <- ffLayer g    \\ sl \\ sj
          return $ l ~** n  \\ sl \\ sj


runNetwork
    :: (Floating (ElemT t), Tensor t)
    => Network t i o
    -> t '[i]
    -> t '[o]
runNetwork (N _ o p) = head' . runTensorOp o . (:< p)

trainNetwork
    :: forall i o t. (SingI i, SingI o, Tensor t, Floating (ElemT t))
    => ElemT t
    -> t '[i]
    -> t '[o]
    -> Network t i o
    -> Network t i o
trainNetwork r x y = \case
    N (s :: Sing os) (o :: TensorOp ('[i] ': os) '[ '[o]]) (p :: Prod t os) ->
      ( let o'   :: TensorOp ('[i] ': os >: '[o]) '[ '[]]
            o' = pappend (sing `SCons` s) sing sing o squaredError
            inp  :: Prod t ('[i] ': os >: '[o])
            inp = x :< p >: y
            grad :: Prod t os
            grad = takeProd (singLength s) (LS LZ :: Length '[ '[o]])
                 . tail'
                 $ gradTensorOp o' inp
            p'   :: Prod t os
            p' = map1 (\(s1 :&: o1 :&: g1) -> withSingI s1 $ TT.zip2 stepFunc o1 g1)
               $ zipProd3 (singProd s) p grad
        in  N s o p'
      ) \\ appendSnoc (singLength s) (Proxy @('[o]))
  where
    stepFunc :: ElemT t -> ElemT t -> ElemT t
    stepFunc o' g' = o' - r * g'

squaredError
    :: forall o. SingI o
    => TensorOp '[ '[o], '[o]] '[ '[] ]
squaredError = (LS (LS LZ), LZ   , TO.zip2      (-)         )
            ~. (LS LZ     , LZ   , TO.replicate (US (US UØ)))
            ~. (LS (LS LZ), LZ   , TO.dot                   )
            ~. OPØ

netTest
    :: PrimMonad m
    => Double
    -> Int
    -> Gen (PrimState m)
    -> m String
netTest rate n g = do
    inps :: [LTensor '[N2]] <- replicateM n (genRand (uniformDistr (-1) 1) g)
    let outs :: [LTensor '[N1]]
        outs = flip map inps $ \v ->
                 if v `inCircle` (fromRational 0.33, 0.33)
                      || v `inCircle` (fromRational (-0.33), 0.33)
                   then fromRational 1
                   else fromRational 0
    net0 :: Network LTensor N2 N1
            <- genNet [ SomeSing (sing :: Sing N10)
                      , SomeSing (sing :: Sing N10)
                      ] g
    let trained = foldl' trainEach net0 (zip inps outs)
          where
            trainEach :: (Known Nat i, Known Nat o)
                      => Network LTensor i o
                      -> (LTensor '[i], LTensor '[o])
                      -> Network LTensor i o
            trainEach nt (i, o) = trainNetwork rate i o nt

        outMat = [ [ render . unScalar . join TT.dot . runNetwork trained $
                       fromJust (TT.fromList [x / 25 - 1,y / 10 - 1])
                   | x <- [0..50] ]
                 | y <- [0..20] ]
        render r | r <= 0.2  = ' '
                 | r <= 0.4  = '.'
                 | r <= 0.6  = '-'
                 | r <= 0.8  = '='
                 | otherwise = '#'
    return $ unlines outMat
  where
    inCircle
        :: LTensor '[N2]
        -> (LTensor '[N2], Double)
        -> Bool
    v `inCircle` (o, r) = let d = v - o
                          in  unScalar (d `TT.dot` d) <= r**2

main :: IO ()
main = withSystemRandom $ \g -> do
    -- n :: Network LTensor N4 N2
    --     <- genNet [SomeSing (sing :: Sing N3), SomeSing (sing :: Sing N2)] g
    -- case n of
    --   N (s :: Sing os) _ (p :: Prod LTensor os) -> do
    --     let p' :: Prod (Sing :&: LTensor) os
    --         p' = zipProd (singProd s) p
    --     traverse1_ (\(s' :&: t) -> putStrLn (show t) \\ s') p'

    putStrLn "Training network..."
    putStrLn =<< netTest 5 75000 g

