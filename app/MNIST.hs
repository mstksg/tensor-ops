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

import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Data.Bifunctor
import           Data.Either.Validation
import           Data.Finite
import           Data.Foldable
import           Data.IDX
import           Data.Kind
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
import           System.Directory
import           System.FilePath
import           System.Random.MWC
import           System.Random.MWC.Distributions
import           TensorOps.Backend.BTensor
import           TensorOps.Learn.NeuralNet
import           TensorOps.Learn.NeuralNet.FeedForward
import           TensorOps.Types
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
              <> value [300] <> showDefault
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

    learn (Proxy @(BTensorV HMatD)) mnistDat oRate oLayers oBatch

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
    :: forall (n :: Nat) (l :: Nat) t. (Fractional (ElemT t), KnownNat n, KnownNat l, Tensor t)
    => (Int, VU.Vector Int)
    -> Either String (t '[n], t '[l])
processDat (l,d) = (,) <$> x <*> y
  where
    x :: Either String (t '[n])
    x = maybe (Left (printf "Bad input vector (Expected %d, got %d)" n (VU.length d))) Right
      . TT.fromList . map ((/255) . fromIntegral)
      $ VU.toList d
    y :: Either String (t '[l])
    y = maybe (Left (printf "Label out of range (Got %d, expected [0,%d) )" l')) Right
      . flip fmap (packFinite (fromIntegral l) :: Maybe (Finite l)) $ \fl ->
          TT.generate $ \(i :< Ø) -> if i == fl then 1 else 0
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
    -> IO ()
learn _ dat rate layers (fromIntegral->batch) = withSystemRandom $ \g -> do
    dat' <- either (ioError . userError . unlines) return
          . validationToEither
          . (traverse . traverse) processDat'
          $ dat

    dat'' <- evaluate $ force dat'
    putStrLn "Data processed."

    let tXY, vXY :: [(t '[784], t '[10])]
        (tXY, vXY) = case dat'' of
                       I t :* I v :* ØV -> (t,v)

        vXY' = (map . second) TT.argMax vXY

    net0 :: Network t 784 10
            <- genNet (layers `zip` repeat (actMap logistic)) actSoftmax g

    printf "rate: %f | batch: %d | layers: %s\n" rate batch (show layers)

    trainEpochs tXY vXY' g net0
  where
    processDat'
        :: (Int, VU.Vector Int)
        -> Validation [String] (t '[784], t '[10])
    processDat' = eitherToValidation . first (:[]) . processDat
    trainEpochs
        :: [(t '[784], t '[10])]
        -> [(t '[784], Finite 10)]
        -> GenIO
        -> Network t 784 10
        -> IO ()
    trainEpochs (V.fromList->tr) vd g = trainEpoch 1
      where
        trainEpoch
            :: Integer
            -> Network t 784 10
            -> IO ()
        trainEpoch e nt0 = do
            printf "[Epoch %d]\n" e
            queue <- evaluate . force =<< uniformShuffle tr g

            nt1 <- trainBatch 1 queue nt0
            trainEpoch (succ e) nt1
          where
            trainBatch
                :: Integer
                -> V.Vector (t '[784], t '[10])
                -> Network t 784 10
                -> IO (Network t 784 10)
            trainBatch b (V.splitAt batch->(xs,xss)) nt
                | V.null xs = return nt
                | otherwise = do
              printf "Batch %d ...\n" b
              (nt', t) <- time . return $ trainAll nt xs
              printf "Trained on %d / %d samples in %s\n" (V.length xs) (length tr) (show t)
              let score = F.fold (validate nt') vd
              printf "Validation: %.2f%% error\n" ((1 - score) * 100)
              trainBatch (succ b) xss nt'
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
        -- trainNetwork squaredError rate' i o nt
    rate' :: ElemT t
    rate' = realToFrac rate


time
    :: NFData a
    => IO a
    -> IO (a, NominalDiffTime)
time x = do
    t1 <- getCurrentTime
    y  <- evaluate . force =<< x
    t2 <- getCurrentTime
    return (y, t2 `diffUTCTime` t1)

