{-# LANGUAGE ViewPatterns, RecordWildCards  #-}

module TestProtocol where

import Protolude

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck
import qualified Test.QuickCheck.Monadic as QCM

import Crypto.Random.Types (MonadRandom(..))
import Crypto.Number.Generate (generateMax)
import qualified Crypto.PubKey.ECC.Generate as Crypto
import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto

import Bulletproofs.Curve
import qualified Bulletproofs.RangeProof as RP
import qualified Bulletproofs.RangeProof.Internal as RP
import qualified Bulletproofs.RangeProof.Verifier as RP

import qualified Bulletproofs.MultiRangeProof as MRP
import qualified Bulletproofs.MultiRangeProof.Verifier as MRP

import Bulletproofs.Utils
import Bulletproofs.Fq as Fq

import TestField

newtype Bin = Bin { unbin :: Int } deriving Show

instance Arbitrary Bin where
  arbitrary = Bin <$> arbitrary `suchThat` flip elem [0,1]

getUpperBound :: Integer -> Integer
getUpperBound n = 2 ^ n

prop_complementaryVector_dotp :: [Bin] -> Property
prop_complementaryVector_dotp ((unbin <$>) -> xs)
  = dotp xs (RP.complementaryVector xs) === 0

prop_complementaryVector_hadamard :: [Bin] -> Property
prop_complementaryVector_hadamard ((toInteger . unbin <$>) -> xs)
  = hadamardp xs (RP.complementaryVector xs) === replicate (length xs) 0

prop_dotp_aL2n :: Property
prop_dotp_aL2n = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  v <- QCM.run $ Fq.random n
  QCM.assert $ RP.reversedEncodeBit n v `dotp` powerVector (Fq.new 2) n == v

prop_challengeComplementaryVector :: Property
prop_challengeComplementaryVector = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  v <- QCM.run $ Fq.random n
  let aL = RP.reversedEncodeBit n v
      aR = RP.complementaryVector aL
  y <- QCM.run $ Fq.random n
  QCM.assert
    $ dotp
      ((aL `fqSubV` powerVector 1 n) `fqSubV` aR)
      (powerVector y n)
      ==
      0

prop_reversedEncodeBitAggr :: Int -> Property
prop_reversedEncodeBitAggr x = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  vs <- QCM.run $ replicateM x $ Fq.random n
  let m = fromIntegral $ length vs
      reversed = RP.reversedEncodeBitMulti n vs
  QCM.assert $ vs == fmap (\j -> dotp (slice n j reversed) (powerVector 2 n)) [1..m]

prop_challengeComplementaryVectorAggr :: Int -> Property
prop_challengeComplementaryVectorAggr x = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  vs <- QCM.run $ replicateM 3 $ Fq.random n
  let aL = RP.reversedEncodeBitMulti n vs
      aR = RP.complementaryVector aL
      m = length vs
  y <- QCM.run $ Fq.random n
  QCM.assert $
    replicate m 0
    ==
    fmap (\j -> dotp ((slice n j aL `fqSubV` powerVector 1 n) `fqSubV` slice n j aR) (powerVector y n)) [1..fromIntegral m]

prop_obfuscateEncodedBits
  :: Fq
  -> Fq
  -> Property
prop_obfuscateEncodedBits y z
  = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  v <- QCM.run $ Fq.random n
  let aL = RP.reversedEncodeBit n v
      aR = RP.complementaryVector aL

  QCM.assert $ RP.obfuscateEncodedBits n aL aR y z == fqSquare z * v

prop_singleInnerProduct
  :: Fq
  -> Fq
  -> Property
prop_singleInnerProduct y z
  = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  v <- QCM.run $ Fq.random n

  let aL = RP.reversedEncodeBit n v
      aR = RP.complementaryVector aL

  QCM.assert $ RP.obfuscateEncodedBitsSingle n aL aR y z == (fqSquare z * v) + RP.delta n 1 y z

setupV :: MonadRandom m => Integer -> m ((Integer, Integer), Crypto.Point)
setupV n = do
  v <- generateMax (2^n)
  vBlinding <- Crypto.scalarGenerate curve
  let vCommit = commit (Fq.new v) (Fq.new vBlinding)
  pure ((v, vBlinding), vCommit)

test_verifyTPolynomial :: TestTree
test_verifyTPolynomial = localOption (QuickCheckTests 5) $
  testProperty "Verify T polynomial" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> generateMax 8
    m <- QCM.run $ (2 ^) <$> generateMax 3
    ctx <- QCM.run $ replicateM m (setupV n)

    proofE <- QCM.run $ runExceptT $ MRP.generateProof (getUpperBound n) (fst <$> ctx)
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) -> do
        let x = shamirX aCommit sCommit t1Commit t2Commit y z
            y = shamirY aCommit sCommit
            z = shamirZ aCommit sCommit y
        QCM.assert $ MRP.verifyTPoly n (snd <$> ctx) proof x y z

test_verifyLRCommitments :: TestTree
test_verifyLRCommitments = localOption (QuickCheckTests 5) $
  testProperty "Verify LR commitments" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> generateMax 8
    m <- QCM.run $ (2 ^) <$> generateMax 3
    ctx <- QCM.run $ replicateM (fromIntegral m) (setupV n)

    proofE <- QCM.run $ runExceptT $ MRP.generateProof (getUpperBound n) (fst <$> ctx)
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) -> do
        let x = shamirX aCommit sCommit t1Commit t2Commit y z
            y = shamirY aCommit sCommit
            z = shamirZ aCommit sCommit y

        QCM.assert $ MRP.verifyLRCommitment n m proof x y z

prop_valueNotInRange :: Property
prop_valueNotInRange = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  ((v, vBlinding), vCommit) <- QCM.run $ setupV n
  let upperBound = getUpperBound n
      vNotInRange = v + upperBound

  proofE <- QCM.run $ runExceptT $ MRP.generateProof upperBound [(vNotInRange, vBlinding)]
  case proofE of
    Left err ->
      QCM.assert $ RP.ValuesNotInRange [vNotInRange] == err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ MRP.verifyProof upperBound [vCommit] proof

prop_invalidUpperBound :: Property
prop_invalidUpperBound = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  ((v, vBlinding), vCommit) <- QCM.run $ setupV n
  let invalidUpperBound = q + 1
  proofE <- QCM.run $ runExceptT $ MRP.generateProof invalidUpperBound [(v, vBlinding)]
  case proofE of
    Left err ->
      QCM.assert $ RP.UpperBoundTooLarge invalidUpperBound == err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ MRP.verifyProof invalidUpperBound [vCommit] proof

prop_differentUpperBound :: Positive Integer -> Property
prop_differentUpperBound (Positive upperBound') = expectFailure . QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  ((v, vBlinding), vCommit) <- QCM.run $ setupV n
  proofE <- QCM.run $ runExceptT $ MRP.generateProof (getUpperBound n) [(v, vBlinding)]
  case proofE of
    Left err -> panic $ show err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ MRP.verifyProof upperBound' [vCommit] proof

test_invalidCommitment :: TestTree
test_invalidCommitment = localOption (QuickCheckTests 20) $
  testProperty "Check invalid commitment" $ QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  ((v, vBlinding), vCommit) <- QCM.run $ setupV n
  let invalidVCommit = commit (Fq.new $ v + 1) (Fq.new vBlinding)
      upperBound = getUpperBound n
  proofE <- QCM.run $ runExceptT $ MRP.generateProof upperBound [(v, vBlinding)]
  case proofE of
    Left err -> panic $ show err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ not $ MRP.verifyProof upperBound [invalidVCommit] proof

test_completeness :: TestTree
test_completeness = localOption (QuickCheckTests 10) $
  testProperty "Test multi range proof completeness" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> generateMax 8
    m <- QCM.run $ (2 ^) <$> generateMax 3
    ctx <- QCM.run $ replicateM (fromIntegral m) (setupV n)
    let upperBound = getUpperBound n

    proofE <- QCM.run $ runExceptT $ MRP.generateProof (getUpperBound n) (fst <$> ctx)
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) ->
        QCM.assert $ MRP.verifyProof upperBound (snd <$> ctx) proof

test_singleRangeProof :: TestTree
test_singleRangeProof = localOption (QuickCheckTests 20) $
  testProperty "Test single range proof completeness" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> generateMax 8
    ((v, vBlinding), vCommit) <- QCM.run $ setupV n
    let upperBound = getUpperBound n

    proofE <- QCM.run $ runExceptT $ RP.generateProof (getUpperBound n) (v, vBlinding)
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) ->
        QCM.assert $ RP.verifyProof upperBound vCommit proof


