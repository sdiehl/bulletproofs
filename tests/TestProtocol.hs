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

  QCM.assert $ RP.obfuscateEncodedBitsSingle n aL aR y z == (fqSquare z * v) + RP.delta n y z

setupV :: MonadRandom m => Integer -> m (Integer, Integer, Crypto.Point)
setupV n = do
  v <- generateMax (2^n)
  vBlinding <- Crypto.scalarGenerate curve
  let vCommit = commit (Fq.new v) (Fq.new vBlinding)
  pure (v, vBlinding, vCommit)

test_verifyTPolynomial :: TestTree
test_verifyTPolynomial = localOption (QuickCheckTests 50) $
  testProperty "Verify T polynomial" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> generateMax 8
    (v, vBlinding, vCommit) <- QCM.run $ setupV n

    proofE <- QCM.run $ runExceptT $ RP.generateProof (getUpperBound n) v vBlinding
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) -> do
        let x = shamirX aCommit sCommit t1Commit t2Commit y z
            y = shamirY aCommit sCommit
            z = shamirZ aCommit sCommit y
        QCM.assert $ RP.verifyTPoly n vCommit proof x y z

test_verifyLRCommitments :: TestTree
test_verifyLRCommitments = localOption (QuickCheckTests 20) $
  testProperty "Verify LR commitments" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> generateMax 8
    (v, vBlinding, vCommit) <- QCM.run $ setupV n

    proofE <- QCM.run $ runExceptT $ RP.generateProof (getUpperBound n) v vBlinding
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) -> do
        let x = shamirX aCommit sCommit t1Commit t2Commit y z
            y = shamirY aCommit sCommit
            z = shamirZ aCommit sCommit y

        QCM.assert $ RP.verifyLRCommitment n proof x y z

prop_valueNotInRange :: Property
prop_valueNotInRange = expectFailure . QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  (v, vBlinding, vCommit) <- QCM.run $ setupV n
  let upperBound = getUpperBound n
      vNotInRange = v + upperBound

  proofE <- QCM.run $ runExceptT $ RP.generateProof upperBound vNotInRange vBlinding
  case proofE of
    Left err -> panic $ show err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ RP.verifyProof upperBound vCommit proof

prop_invalidUpperBound :: Property
prop_invalidUpperBound = expectFailure . QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  (v, vBlinding, vCommit) <- QCM.run $ setupV n
  let invalidUpperBound = q + 1
  proofE <- QCM.run $ runExceptT $ RP.generateProof invalidUpperBound v vBlinding
  case proofE of
    Left err -> panic $ show err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ RP.verifyProof invalidUpperBound vCommit proof

prop_differentUpperBound :: Positive Integer -> Property
prop_differentUpperBound (Positive upperBound') = expectFailure . QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  (v, vBlinding, vCommit) <- QCM.run $ setupV n
  proofE <- QCM.run $ runExceptT $ RP.generateProof (getUpperBound n) v vBlinding
  case proofE of
    Left err -> panic $ show err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ RP.verifyProof upperBound' vCommit proof

test_invalidCommitment :: TestTree
test_invalidCommitment = localOption (QuickCheckTests 20) $
  testProperty "Check invalid commitment" $ QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> generateMax 8
  (v, vBlinding, vCommit) <- QCM.run $ setupV n
  let invalidVCommit = commit (Fq.new $ v + 1) (Fq.new vBlinding)
      upperBound = getUpperBound n
  proofE <- QCM.run $ runExceptT $ RP.generateProof upperBound v vBlinding
  case proofE of
    Left err -> panic $ show err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ not $ RP.verifyProof upperBound invalidVCommit proof

test_completeness :: TestTree
test_completeness = localOption (QuickCheckTests 20) $
  testProperty "Test range proof completeness" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> generateMax 8
    (v, vBlinding, vCommit) <- QCM.run $ setupV n
    let upperBound = getUpperBound n
    proofE <- QCM.run $ runExceptT $ RP.generateProof upperBound v vBlinding
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) ->
        QCM.assert $ RP.verifyProof upperBound vCommit proof

