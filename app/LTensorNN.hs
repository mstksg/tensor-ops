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

-- import           Data.Singletons.Prelude.Num
-- import           Data.Type.Combinator
-- import           Data.Type.Index
-- import           Data.Type.Nat
-- import           Data.Type.Nat.Quote
-- import           GHC.TypeLits
-- import           Statistics.Distribution
-- import           Type.Class.Higher.Util
-- import           Type.Class.Known
-- import           Type.Family.Nat
-- import           Type.Family.Nat.Util
import           Control.Category
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Control.Monad.Primitive
import           Data.Kind
import           Data.List hiding                ((\\))
import           Data.Maybe
import           Data.Singletons
import           Data.Singletons.Prelude.List    (Sing(..))
import           Data.Singletons.TypeLits
import           Data.Time.Clock
import           Data.Type.Conjunction
import           Data.Type.Length
import           Data.Type.Product               as TCP
import           Data.Type.Product.Util
import           Data.Type.Sing
import           Data.Type.Uniform
import           Prelude hiding                  ((.), id)
import           Statistics.Distribution.Normal
import           Statistics.Distribution.Uniform
import           System.Random.MWC
import           TensorOps.Backend.LTensor
import           TensorOps.Backend.VTensor
import           TensorOps.Gradient
import           TensorOps.Run
import           TensorOps.Types
import           Type.Class.Higher
import           Type.Class.Witness hiding       (inner)
import           Type.Family.List
import           Type.Family.List.Util
import           Type.NatKind
import qualified TensorOps.TOp                   as TO
import qualified TensorOps.Tensor                as TT


logistic
    :: forall a. Floating a
    => a
    -> a
logistic x = 1 / (1 + exp (- x))

sigmoid
    :: forall a. Floating a
    => a
    -> a
sigmoid x = (tanh x + 2) / 2

relu
    :: forall a. Floating a
    => a
    -> a
relu x = x * ((signum x + 1)/ 2)

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
  where
    ffLayer'
        :: TensorOp '[ '[i], '[o,i], '[o]] '[ '[o] ]
    ffLayer' = (LS (LS LZ), LS LZ, TO.swap                   )
            ~. (LS (LS LZ), LS LZ, GMul    (LS LZ) (LS LZ) LZ)
            ~. (LS (LS LZ), LZ   , TO.zip2 (+)               )
            ~. (LS LZ     , LZ   , TO.map  logistic          )
            -- ~. (LS LZ     , LZ   , TO.map  sigmoid           )
            -- ~. (LS LZ     , LZ   , TO.map  relu              )
            ~. OPØ


genNet
    :: forall k o i m (t :: [k] -> Type). (SingI o, SingI i, PrimMonad m, Tensor t)
    => [Integer]
    -> Gen (PrimState m)
    -> m (Network t i o)
genNet xs0 g = go sing xs0
  where
    go  :: forall (j :: k). ()
        => Sing j
        -> [Integer]
        -> m (Network t j o)
    go sj = \case
      []   -> ffLayer g           \\ sj
      x:xs -> withNatKind x $ \sl -> do
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
    :: forall k m (t :: [k] -> Type).
     ( PrimMonad m
     , Tensor t
     , ElemT t ~ Double
     )
    => Proxy t
    -> Double
    -> Int
    -> [Integer]
    -> Gen (PrimState m)
    -> m String
netTest _ rate n hs g = withSingI (sFromNat @k (SNat @1)) $
                        withSingI (sFromNat @k (SNat @2)) $ do
    inps :: [t '[FromNat 2]] <- replicateM n (genRand (uniformDistr (-1) 1) g)
    let outs :: [t '[FromNat 1]]
        outs = flip map inps $ \v -> TT.konst $
                 if v `inCircle` (TT.konst 0.33, 0.33)
                      || v `inCircle` (TT.konst (-0.33), 0.33)
                   then 1
                   else 0
    net0 :: Network t (FromNat 2) (FromNat 1)
            <- genNet hs g
    let trained = foldl' trainEach net0 (zip inps outs)
          where
            trainEach :: (SingI i, SingI o)
                      => Network t i o
                      -> (t '[i], t '[o])
                      -> Network t i o
            trainEach nt (i, o) = trainNetwork rate i o nt

        outMat = [ [ render . TT.unScalar . join TT.dot . runNetwork trained $
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
        :: SingI n
        => t '[n]
        -> (t '[n], Double)
        -> Bool
    v `inCircle` (o, r) = let d = TT.zip2 (-) v o
                          in  TT.unScalar (d `TT.dot` d) <= r**2

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
    -- (r1, t1) <- time $ netTest (Proxy @LTensor) 1 50000 [5,5] g
    -- putStrLn r1
    -- print t1
    (r2, t2) <- time $ netTest (Proxy @VTensor) 1 50000 [5,5] g
    putStrLn r2
    print t2

time
    :: NFData a
    => IO a
    -> IO (a, NominalDiffTime)
time x = do
    t1 <- getCurrentTime
    y  <- evaluate . force =<< x
    t2 <- getCurrentTime
    return (y, t2 `diffUTCTime` t1)



