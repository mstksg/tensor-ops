{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

import           Control.Category
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Data.Foldable
import           Data.Kind
import           Data.List hiding                      ((\\))
import           Data.Maybe
import           Data.Monoid
import           Data.Nested
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Data.Time.Clock
import           Options.Applicative
import           Prelude hiding                        ((.), id)
import           Statistics.Distribution.Uniform
import           System.Random.MWC
import           TensorOps.Backend.BTensor
import           TensorOps.Backend.NTensor
import           TensorOps.Model.NeuralNet.FeedForward
import           TensorOps.Model.NeuralNet
import           TensorOps.NatKind
import           TensorOps.Types
import           Text.PrettyPrint.ANSI.Leijen hiding   ((<>),(<$>))
import           Text.Printf
import qualified Data.String.Here                      as H
import qualified TensorOps.Tensor                      as TT


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
    ((inps,outs),tp) <- time $ do
      inps :: [t '[FromNat 2]] <- replicateM n (genRand (uniformDistr (-1) 1) g)
      let outs :: [t '[FromNat 1]]
          outs = flip map inps $ \v -> TT.konst $
                   if v `inCircle` (TT.konst 0.33, 0.33)
                        || v `inCircle` (TT.konst (-0.33), 0.33)
                     then 1
                     else 0
      evaluate . force $ (inps, outs)
    printf "Generated test points (%s)\n" (show tp)
    net0 :: Network t (FromNat 2) (FromNat 1)
            <- nmap logistic <$> genNet logistic hs g
    let trained = foldl' trainEach net0 (zip inps outs)
          where
            trainEach :: (SingI i, SingI o)
                      => Network t i o
                      -> (t '[i], t '[o])
                      -> Network t i o
            trainEach nt (i, o) = nt `deepseq` trainNetwork rate i o nt
    (trained', tn) <- time $ return trained
    printf "Network trained (%s)\n" (show tn)
    let outMat = [ [ render . TT.unScalar . join TT.dot . runNetwork trained' $
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
              , oTests   :: [TestT]
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
              <> value 50000 <> showDefault
               )
         <*> option auto
               ( long "layers" <> short 'l' <> metavar "LIST"
              <> help "List of hidden layer sizes"
              <> value [12,8] <> showDefault
               )
         <*> (nub <$> (some (argument readBackend (metavar "BACKEND")))
               <|> pure [TTBLAS TBHMat]
             )

main :: IO ()
main = withSystemRandom $ \g -> do
    O{..} <- execParser $ info (helper <*> opts)
        ( fullDesc
       <> header "tensor-ops-dots - train neural nets with tensor-ops"
       <> progDescDoc (Just d)
        )

    printf "rate: %f | samps: %d | layers: %s\n" oRate oSamples (show oNetwork)

    forM_ oTests $ \t -> do
      printf "Training %s network ...\n" (ttLong t)
      let tester :: Double -> Int -> [Integer] -> GenIO -> IO String
          tester = case t of
            TTNested TVList -> netTest (Proxy @NTensorL)
            TTNested TVVect -> netTest (Proxy @NTensorV)
            TTBLAS   TBHMat -> netTest (Proxy @(BTensorV (HMat Double)))
      putStrLn =<< tester oRate oSamples oNetwork g
  where
    d :: Doc
    d = string [H.here|
Trains a feed-forward neural network on a 2D classifier using tensor-ops
machinery, with the given backends.  (If none provided, backend defaults to 'b')
|]
     <$$> mempty
     <$$> string "Backends:"
     <$$> vsep [ string $ printf "- %s: %s" (ttShort t) (ttLong t)
               | t <- allTests ]

time
    :: NFData a
    => IO a
    -> IO (a, NominalDiffTime)
time x = do
    t1 <- getCurrentTime
    y  <- evaluate . force =<< x
    t2 <- getCurrentTime
    return (y, t2 `diffUTCTime` t1)


data TestT = TTNested TestV
           | TTBLAS   TestB
           deriving (Show, Eq, Ord)
data TestV = TVList
           | TVVect
           deriving (Show, Eq, Ord)
data TestB = TBHMat
           deriving (Show, Eq, Ord)

allTests :: [TestT]
allTests = ([TTNested] <*> [TVList, TVVect]) ++ [TTBLAS TBHMat]

readBackend :: ReadM TestT
readBackend = eitherReader $ \s -> case s of
    "nl" -> Right $ TTNested TVList
    "nv" -> Right $ TTNested TVVect
    "b"  -> Right $ TTBLAS   TBHMat
    o    -> Left  $ "Unknown backend: " ++ o

ttShort
    :: TestT
    -> String
ttShort = \case
    TTNested v -> 'n' : tvShort v
    TTBLAS   b -> 'b' : tbShort b
  where
    tvShort = \case
      TVList -> "l"
      TVVect -> "v"
    tbShort = \case
      TBHMat -> ""

ttLong
    :: TestT
    -> String
ttLong = \case
    TTNested v -> printf "Nested (%s)" (tvLong v)
    TTBLAS   b -> printf "BLAS (%s)" (tbLong b)
  where
    tvLong = \case
      TVList -> "List"
      TVVect -> "Vector"
    tbLong = \case
      TBHMat -> "HMatrix"
