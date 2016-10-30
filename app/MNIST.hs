{-# LANGUAGE ApplicativeDo       #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

import           Control.Arrow                         ((&&&))
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State.Strict
import           Control.Monad.Trans.Writer.Strict
import           Data.Bifunctor
import           Data.Either.Validation
import           Data.Finite
import           Data.Foldable
import           Data.IDX
import           Data.Kind
import           Data.Maybe
import           Data.Monoid
import           Data.Profunctor
import           Data.Proxy
import           Data.String
import           Data.Time.Clock
import           Data.Type.Combinator
import           Data.Type.Product                     as TCP
import           Data.Type.Vector
import           GHC.Generics                          (Generic)
import           GHC.TypeLits
import           Options.Applicative hiding            (ParserResult(..))
import           Statistics.Distribution.Uniform
import           System.Directory
import           System.FilePath
import           System.Random.MWC
import           System.Random.MWC.Distributions
import           TensorOps.Backend.BTensor
import           TensorOps.Learn.NeuralNet
import           TensorOps.Learn.NeuralNet.FeedForward
import           TensorOps.Types hiding                ((&&&))
import           Text.Printf
import           Type.Class.Higher.Util
import           Type.Family.Nat
import qualified Codec.Compression.GZip                as GZ
import qualified Control.Foldl                         as F
import qualified Data.ByteString.Lazy                  as BS
import qualified Data.Vector                           as V
import qualified Data.Vector.Unboxed                   as VU
import qualified Network.HTTP.Simple                   as HTTP
import qualified TensorOps.Tensor                      as TT

mnistBase :: String
mnistBase = "http://yann.lecun.com/exdb/mnist"

mnistFiles :: Matrix '[N2, N2] FilePath
mnistFiles = ("train-images-idx3-ubyte" :+ "train-labels-idx1-ubyte" :+ ØV)
          :* ("t10k-images-idx3-ubyte"  :+ "t10k-labels-idx1-ubyte"  :+ ØV)
          :* ØV

data Opts = O { oRate    :: Double
              , oLayers  :: [Integer]
              , oBatch   :: Integer
              , oDataDir :: FilePath
              , oInduce  :: Maybe (Finite 10)
              }
    deriving (Show, Eq, Generic)

opts :: Parser Opts
opts = O <$> option auto
               ( long "rate" <> short 'r' <> metavar "STEP"
              <> help "Neural network learning rate"
              <> value 0.01 <> showDefault
               )
         <*> option auto
               ( long "layers" <> short 'l' <> metavar "LIST"
              <> help "List of hidden layer sizes"
              <> value [300,150] <> showDefault
               )
         <*> option auto
               ( long "batch" <> short 'b' <> metavar "AMOUNT"
              <> help "Training batch size"
              <> value 1000 <> showDefault
               )
         <*> strOption
               ( long "data" <> short 'd' <> metavar "PATH"
              <> help "Directory to store/cache MNIST data files"
              <> value "data/mnist" <> showDefaultWith id
               )
         <*> optional (
               option readFin
                 ( long "induce" <> short 'i' <> metavar "DIGIT"
                <> help ("Every batch, attempt to induce an image "
                      ++ "of the given digit with the trained network"
                        )
                 )
             )
  where
    readFin :: forall n. KnownNat n => ReadM (Finite n)
    readFin = do
        i <- auto
        case packFinite i of
          Nothing -> readerError $
            printf "Number %d out of range (%d)" i (natVal (Proxy @n) - 1)
          Just x  -> return x

main :: IO ()
main = do
    O{..} <- execParser $ info (helper <*> opts)
        ( fullDesc
       <> header "tensor-ops-mnist - train neural nets on MNIST data set"
       <> progDesc (unlines ["Simple test of tensor-ops tensors (with hmatrix"
                            ,"backend) on MNIST classification challenge"
                            ]
                   )
        )

    mnistDat <- loadData oDataDir
    putStrLn "Loaded data."

    learn (Proxy @(BTensorV HMatD)) mnistDat oRate oLayers oBatch oInduce

loadData
    :: FilePath
    -> IO (Vec N2 [(Int, VU.Vector Int)])
loadData dataDir = do
    createDirectoryIfMissing True dataDir

    printf "Loading data from %s\n" dataDir
    mnistBs <- forM mnistFiles $ \u -> do
      BS.readFile (dataDir </> u) `catch` \(_ :: IOException) -> do
        printf "'%s' not found; downloading from %s ...\n" u mnistBase
        b <- GZ.decompress . HTTP.getResponseBody
               <$> HTTP.httpLBS (fromString (mnistBase </> u -<.> "gz"))
        BS.writeFile (dataDir </> u) b
        return b

    let f   :: Vec N2 FilePath
            -> Vec N2 BS.ByteString
            -> I (Validation [String] (FilePath, FilePath, IDXData, IDXLabels))
        f (I uIm :* I uLb :* ØV) (I bIm :* I bLb :* ØV) = I $ do
            im <- maybe (Failure [printf "Could not decode image %s." uIm]) Success
                    $ decodeIDX bIm
            lb <- maybe (Failure [printf "Could not decode labels %s." uLb]) Success
                    $ decodeIDXLabels bLb
            pure (uIm, uLb, im, lb)

        mnistDat' :: Either [String] (Vec N2 [(Int, VU.Vector Int)])
        mnistDat' = do
          imlb <- validationToEither . sequenceA $ vap f mnistFiles mnistBs
          forM imlb $ \(uIm, uLb, im, lb) ->
            maybe (Left [printf "Could not combine %s and %s." uIm uLb]) Right
              $ labeledIntData lb im

    evaluate . force
        =<< either (ioError . userError . unlines) return mnistDat'

processDat
    :: forall (n :: Nat) (l :: Nat) t.
     ( Fractional (ElemT t)
     , KnownNat n
     , KnownNat l
     , Tensor t
     )
    => (Int, VU.Vector Int)
    -> Either String (t '[n], (t '[l], Finite l))
processDat (l,d) = (,) <$> x <*> y
  where
    x :: Either String (t '[n])
    x = maybe (Left (printf "Bad input vector (Expected %d, got %d)" n (VU.length d))) Right
      . TT.fromList . map ((/255) . fromIntegral)
      $ VU.toList d
    y :: Either String (t '[l], Finite l)
    y = maybe (Left (printf "Label out of range (Got %d, expected [0,%d) )" l')) Right
      . fmap (TT.oneHot 1 0 &&& id)
      $ packFinite (fromIntegral l)
    n :: Integer
    n = natVal (Proxy @n)
    l' :: Integer
    l' = natVal (Proxy @l)

learn
    :: forall (t :: [Nat] -> Type).
     ( Tensor t
     , RealFloat (ElemT t)
     , NFData1 t
     , NFData (t '[784])
     , NFData (t '[10])
     )
    => Proxy t
    -> Vec N2 [(Int, VU.Vector Int)]
    -> Double
    -> [Integer]
    -> Integer
    -> Maybe (Finite 10)
    -> IO ()
learn _ dat rate layers (fromIntegral->batch) ind =
      withSystemRandom $ \g -> do
    dat' <- either (ioError . userError . unlines) return
          . validationToEither
          . (traverse . traverse) processDat'
          $ dat

    dat'' <- evaluate $ force dat'
    putStrLn "Data processed."

    let tXY, vXY :: [(t '[784], (t '[10], Finite 10))]
        (tXY, vXY) = case dat'' of
                       I t :* I v :* ØV -> (t,v)

    net0 :: Network t 784 10
            <- genNet (layers `zip` repeat (actMap logistic)) actSoftmax g
    x0 <- genRand (uniformDistr 0 1) g

    printf "rate: %f | batch: %d | layers: %s\n" rate batch (show layers)
    forM_ ind $ \i ->
      printf "inducing: %d\n" (getFinite i)

    trainEpochs tXY ((map . second) snd vXY) g net0 x0
  where
    ind' :: Maybe (t '[10])
    ind' = TT.oneHot 1 0 <$> ind
    processDat'
        :: (Int, VU.Vector Int)
        -> Validation [String] (t '[784], (t '[10], Finite 10))
    processDat' = eitherToValidation . first (:[]) . processDat
    trainEpochs
        :: [(t '[784], (t '[10], Finite 10))]
        -> [(t '[784], Finite 10)]
        -> GenIO
        -> Network t 784 10
        -> t '[784]
        -> IO ()
    trainEpochs (V.fromList->tr) vd g = trainEpoch 1
      where
        trainEpoch
            :: Integer
            -> Network t 784 10
            -> t '[784]
            -> IO ()
        trainEpoch e nt0 xi0 = do
            printf "[Epoch %d]\n" e
            queue <- evaluate . force =<< uniformShuffle tr g

            (nt1, xi1) <- trainBatch 1 queue nt0 xi0
            trainEpoch (succ e) nt1 xi1
          where
            trainBatch
                :: Integer
                -> V.Vector (t '[784], (t '[10], Finite 10))
                -> Network t 784 10
                -> t '[784]
                -> IO (Network t 784 10, t '[784])
            trainBatch b (V.splitAt batch->(xs,xss)) nt xi
                | V.null xs = return (nt, xi)
                | otherwise = do
              printf "Batch %d ...\n" b
              (nt', t) <- time . return $ trainAll nt ((fmap . second) fst xs)
              printf "Trained on %d / %d samples in %s\n" (V.length xs) (length tr) (show t)
              let tscore = F.fold (validate nt') ((fmap . second) snd xs)
                  vscore = F.fold (validate nt') vd
              printf "Training:   %.2f%% error\n" ((1 - tscore) * 100)
              printf "Validation: %.2f%% error\n" ((1 - vscore) * 100)
              xi' <- fmap (fromMaybe xi) . forM ind' $ \i -> do
                  putStrLn (renderOut xi)
                  let xi' = induceNum nt' i 0.001 10000 xi
                  putStrLn (renderOut xi')
                  return xi'
              trainBatch (succ b) xss nt' xi'
        validate
            :: Network t 784 10
            -> F.Fold (t '[784], Finite 10) Double
        validate n = (\s l -> fromIntegral s / fromIntegral l)
                 <$> lmap (uncurry f) F.sum
                 <*> F.length
          where
            f :: t '[784] -> Finite 10 -> Int
            f x r | TT.argMax (runNetwork n x) == r = 1
                  | otherwise                       = 0
    trainAll
        :: Foldable f
        => Network t 784 10
        -> f (t '[784], t '[10])
        -> Network t 784 10
    trainAll = foldl' $ \nt (i,o) -> nt `deepseq`
        trainNetwork crossEntropy rate' i o nt
    rate' :: ElemT t
    rate' = realToFrac rate
    induceNum
        :: Network t 784 10
        -> t '[10]
        -> ElemT t
        -> Int
        -> t '[784]
        -> t '[784]
    induceNum n t r = go
      where
        go i x
          | i == 0    = x
          | otherwise = let x' = induceNetwork crossEntropy r t n x
                        in  x' `deepseq` go (i - 1) x'

time
    :: NFData a
    => IO a
    -> IO (a, NominalDiffTime)
time x = do
    t1 <- getCurrentTime
    y  <- evaluate . force =<< x
    t2 <- getCurrentTime
    return (y, t2 `diffUTCTime` t1)

renderOut
    :: forall t. (Tensor t, Real (ElemT t))
    => t '[784]
    -> String
renderOut = unlines
          . ($ [])
          . appEndo
          . execWriter
          . execStateT (replicateM 28 go)
          . TT.toList
  where
    go :: StateT [ElemT t] (Writer (Endo [String])) ()
    go = do
        x <- state $ splitAt 28
        lift . tell . Endo . (++) . (:[]) $
            map (render . realToFrac)
          . concatMap (\y -> [y,y])
          $ x
    render :: Double -> Char
    render r | r <= 0.2  = ' '
             | r <= 0.4  = '.'
             | r <= 0.8  = '-'
             | r <= 1.9  = '='
             | otherwise = '#'
