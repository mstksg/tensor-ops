{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

import           Control.Category
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Control.Monad.Primitive
import           Data.Kind
import           Data.List hiding                ((\\))
import           Data.Maybe
import           Data.Nested
import           Data.Singletons
import           Data.Singletons.Prelude.List    (Sing(..))
import           Data.Singletons.TypeLits
import           Data.Time.Clock
import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Product               as TCP
import           Data.Type.Product.Util
import           Data.Type.Sing
import           Data.Type.Uniform
import           Options.Applicative
import           Prelude hiding                  ((.), id)
import           Statistics.Distribution.Normal
import           Statistics.Distribution.Uniform
import           System.Random.MWC
import           TensorOps.Backend.NTensor
import           TensorOps.Gradient
import           TensorOps.Run
import           TensorOps.Types
import           Text.Printf
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

data Network :: ([k] -> Type) -> k -> k -> Type where
    N :: { _nsOs    :: !(Sing os)
         , _nOp     :: !(TensorOp ('[i] ': os) '[ '[o] ])
         , _nParams :: !(Prod t os)
         } -> Network t i o

instance Nesting1 Proxy NFData t => NFData (Network t i o) where
    rnf = \case
      N (s :: Sing os) _ p
        -> p `deepseq` ()
             \\ (nesting1Every (Proxy @t) (map1 (\_ -> Proxy) (singProd s))
                    :: Wit (Every NFData (t <$> os))
                )

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
    :: forall k (t :: [k] -> Type).
     ( Tensor t
     , ElemT t ~ Double
     , NFData (t '[FromNat 1])
     , NFData (t '[FromNat 2])
     , Nesting1 Proxy NFData t
     )
    => Proxy t
    -> Double
    -> Int
    -> [Integer]
    -> GenIO
    -> IO String
netTest _ rate n hs g = withSingI (sFromNat @k (SNat @1)) $
                        withSingI (sFromNat @k (SNat @2)) $ do
    ((inps,outs),t) <- time $ do
      inps :: [t '[FromNat 2]] <- replicateM n (genRand (uniformDistr (-1) 1) g)
      let outs :: [t '[FromNat 1]]
          outs = flip map inps $ \v -> TT.konst $
                   if v `inCircle` (TT.konst 0.33, 0.33)
                        || v `inCircle` (TT.konst (-0.33), 0.33)
                     then 1
                     else 0
      evaluate . force $ (inps, outs)
    printf "Generated test points (%s)\n" (show t)
    net0 :: Network t (FromNat 2) (FromNat 1)
            <- genNet hs g
    let trained = foldl' trainEach net0 (zip inps outs)
          where
            trainEach :: (SingI i, SingI o)
                      => Network t i o
                      -> (t '[i], t '[o])
                      -> Network t i o
            trainEach nt (i, o) = nt `deepseq` trainNetwork rate i o nt

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

data Opts = O { oRate    :: Double
              , oSamples :: Int
              , oNetwork :: [Integer]
              , oNoList  :: Bool
              , oNoVect :: Bool
              }

opts :: Parser Opts
opts = O <$> option auto
               ( long "rate" <> short 'r' <> metavar "STEP"
              <> help "Neural network learning rate"
              <> value 1 <> showDefault
               )
         <*> option auto
               ( long "samps" <> short 's' <> metavar "COUNT"
              <> help "Number of samples to train the network on"
              <> value 100000 <> showDefault
               )
         <*> option auto
               ( long "layers" <> short 'l' <> metavar "LIST"
              <> help "List of hidden layer sizes"
              <> value [8,8] <> showDefault
               )
         <*> switch ( long "nolist" <> help "Do not run the nested linked list backend")
         <*> switch ( long "novect" <> help "Do not run the nested vector backend")

main :: IO ()
main = withSystemRandom $ \g -> do
    O{..} <- execParser $ info (helper <*> opts)
                            ( fullDesc
                           <> header "tensor-ops-neural-nets - train neural nets with tensor-ops"
                           <> progDesc ( "Implements a simple feed-forward neural network to "
                                      <> "train on a simple 2D input using tensor-ops machinery."
                                       )
                            )

    printf "rate: %f | samps: %d | layers: %s\n" oRate oSamples (show oNetwork)
    unless oNoList $ do
      putStrLn "Training nested linked list network..."
      (r1, t1) <- time $ netTest (Proxy @LTensor) oRate oSamples oNetwork g
      putStrLn r1
      print t1
    unless oNoVect $ do
      putStrLn "Training nested vector network..."
      (r2, t2) <- time $ netTest (Proxy @VTensor) oRate oSamples oNetwork g
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



