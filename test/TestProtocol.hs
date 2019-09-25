{-# LANGUAGE ViewPatterns, RecordWildCards, ScopedTypeVariables  #-}

module TestProtocol where

import Protolude

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck.Monadic as QCM

import Control.Monad.Random (MonadRandom, getRandomR)
import Data.Field.Galois (PrimeField(..), rnd)
import Data.Curve.Weierstrass.SECP256K1 (Fr, PA, _r)

import qualified Bulletproofs.RangeProof as RP
import qualified Bulletproofs.RangeProof.Internal as RP
import qualified Bulletproofs.MultiRangeProof as MRP
import qualified Bulletproofs.MultiRangeProof.Verifier as MRP
import Bulletproofs.Utils

newtype Bin = Bin { unbin :: Int } deriving Show

instance Arbitrary Bin where
  arbitrary = Bin <$> arbitrary `suchThat` flip elem [0,1]

getUpperBound :: Integer -> Integer
getUpperBound n = 2 ^ n

prop_complementaryVector_dot :: [Bin] -> Property
prop_complementaryVector_dot ((unbin <$>) -> xs)
  = dot xs (RP.complementaryVector xs) === 0

prop_complementaryVector_hadamard :: [Bin] -> Property
prop_complementaryVector_hadamard ((toInteger . unbin <$>) -> xs)
  = hadamard xs (RP.complementaryVector xs) === replicate (length xs) 0

prop_dot_aL2n :: Property
prop_dot_aL2n = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  v <- QCM.run $ fromInteger <$> randomN n
  QCM.assert $ RP.reversedEncodeBit n v `dot` powerVector 2 n == v

prop_challengeComplementaryVector :: Property
prop_challengeComplementaryVector = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  v <- QCM.run $ fromInteger <$> randomN n
  let aL = RP.reversedEncodeBit n v
      aR = RP.complementaryVector aL
  y <- QCM.run $ fromInteger <$> randomN n
  QCM.assert
    $ dot
      ((aL ^-^ powerVector 1 n) ^-^ aR)
      (powerVector y n)
      ==
      0

prop_reversedEncodeBitAggr :: Int -> Property
prop_reversedEncodeBitAggr x = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  vs <- QCM.run $ ((<$>) fromInteger) <$> replicateM x (randomN n)
  let m = fromIntegral $ length vs
      reversed = RP.reversedEncodeBitMulti n vs
  QCM.assert $ vs == fmap (\j -> dot (slice n j reversed) (powerVector 2 n)) [1..m]

prop_challengeComplementaryVectorAggr :: Int -> Property
prop_challengeComplementaryVectorAggr x = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  vs <- QCM.run $ ((<$>) fromInteger) <$> replicateM 3 (randomN n)
  let aL = RP.reversedEncodeBitMulti n vs
      aR = RP.complementaryVector aL
      m = length vs
  y <- QCM.run $ fromInteger <$> randomN n
  QCM.assert $
    replicate m 0
    ==
    fmap (\j -> dot ((slice n j aL ^-^ powerVector 1 n) ^-^ slice n j aR) (powerVector y n)) [1..fromIntegral m]

prop_obfuscateEncodedBits
  :: Fr
  -> Fr
  -> Property
prop_obfuscateEncodedBits y z
  = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  v <- QCM.run $ fromInteger <$> randomN n
  let aL = RP.reversedEncodeBit n v
      aR = RP.complementaryVector aL

  QCM.assert $ RP.obfuscateEncodedBits n aL aR y z == (z ^ 2) * v

prop_singleInnerProduct
  :: Fr
  -> Fr
  -> Property
prop_singleInnerProduct y z
  = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  v <- QCM.run $ fromInteger <$> randomN n

  let aL = RP.reversedEncodeBit n v
      aR = RP.complementaryVector aL

  QCM.assert $ RP.obfuscateEncodedBitsSingle n aL aR y z == ((z ^ 2) * v) + RP.delta n 1 y z

setupV :: MonadRandom m => Integer -> m ((Fr, Fr), PA)
setupV n = do
  v <- fromInteger <$> getRandomR (0, 2^n - 1)
  vBlinding <- rnd
  let vCommit = commit v vBlinding
  pure ((v, vBlinding), vCommit)

test_verifyTPolynomial :: TestTree
test_verifyTPolynomial = localOption (QuickCheckTests 5) $
  testProperty "Verify T polynomial" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
    m <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 3)
    ctx <- QCM.run $ replicateM m (setupV n)

    proofE <- QCM.run $ runExceptT $ MRP.generateProof (getUpperBound n) (fst <$> ctx)
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) -> do
        let x, y, z :: Fr
            x = shamirX aCommit sCommit t1Commit t2Commit y z
            y = shamirY aCommit sCommit
            z = shamirZ aCommit sCommit y
        QCM.assert $ MRP.verifyTPoly n (snd <$> ctx) proof x y z

test_verifyLRCommitments :: TestTree
test_verifyLRCommitments = localOption (QuickCheckTests 5) $
  testProperty "Verify LR commitments" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
    m <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 3)
    ctx <- QCM.run $ replicateM (fromIntegral m) (setupV n)

    proofE <- QCM.run $ runExceptT $ MRP.generateProof (getUpperBound n) (fst <$> ctx)
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) -> do
        let x, y, z :: Fr
            x = shamirX aCommit sCommit t1Commit t2Commit y z
            y = shamirY aCommit sCommit
            z = shamirZ aCommit sCommit y

        QCM.assert $ MRP.verifyLRCommitment n m proof x y z

prop_valueNotInRange :: Property
prop_valueNotInRange = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  ((v, vBlinding), vCommit) <- QCM.run $ setupV n
  let upperBound = getUpperBound n
      vNotInRange = fromInteger (fromP v + upperBound)

  proofE <- QCM.run $ runExceptT $ MRP.generateProof upperBound [(vNotInRange, vBlinding)]
  case proofE of
    Left err ->
      QCM.assert $ RP.ValuesNotInRange [vNotInRange] == err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ MRP.verifyProof upperBound [vCommit] proof

prop_invalidUpperBound :: Property
prop_invalidUpperBound = QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  ((v, vBlinding), vCommit) <- QCM.run $ setupV n
  let invalidUpperBound = fromIntegral $ _r + 1
  proofE <- QCM.run $ runExceptT $ MRP.generateProof invalidUpperBound [(v, vBlinding)]
  case proofE of
    Left err ->
      QCM.assert $ RP.UpperBoundTooLarge invalidUpperBound == err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ MRP.verifyProof invalidUpperBound [vCommit] proof

prop_differentUpperBound :: Positive Integer -> Property
prop_differentUpperBound (Positive upperBound') = expectFailure . QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  ((v, vBlinding), vCommit) <- QCM.run $ setupV n
  proofE <- QCM.run $ runExceptT $ MRP.generateProof (getUpperBound n) [(v, vBlinding)]
  case proofE of
    Left err -> panic $ show err
    Right (proof@RP.RangeProof{..}) ->
      QCM.assert $ MRP.verifyProof upperBound' [vCommit] proof

test_invalidCommitment :: TestTree
test_invalidCommitment = localOption (QuickCheckTests 20) $
  testProperty "Check invalid commitment" $ QCM.monadicIO $ do
  n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
  ((v, vBlinding), vCommit) <- QCM.run $ setupV n
  let invalidVCommit = commit (v + 1) vBlinding
      upperBound = getUpperBound n
  proofE <- QCM.run $ runExceptT $ MRP.generateProof upperBound [(v, vBlinding)]
  case proofE of
    Left err -> panic $ show err
    Right (proof@(RP.RangeProof{..})) ->
      QCM.assert $ not $ MRP.verifyProof upperBound [invalidVCommit] proof

test_multiRangeProof_completeness :: TestTree
test_multiRangeProof_completeness = localOption (QuickCheckTests 5) $
  testProperty "Test multi range proof completeness" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
    m <- QCM.run $ getRandomR (1 :: Integer, 10)
    ctx <- QCM.run $ replicateM (fromIntegral m) (setupV n)
    let upperBound = getUpperBound n

    proofE <- QCM.run $ runExceptT $ MRP.generateProof (getUpperBound n) (fst <$> ctx)
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) ->
        QCM.assert $ MRP.verifyProof upperBound (snd <$> ctx) proof

test_singleRangeProof_completeness :: TestTree
test_singleRangeProof_completeness = localOption (QuickCheckTests 20) $
  testProperty "Test single range proof completeness" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> getRandomR (0 :: Integer, 7)
    ((v, vBlinding), vCommit) <- QCM.run $ setupV n
    let upperBound = getUpperBound n

    proofE <- QCM.run $ runExceptT $ RP.generateProof (getUpperBound n) (v, vBlinding)
    case proofE of
      Left err -> panic $ show err
      Right (proof@RP.RangeProof{..}) ->
        QCM.assert $ RP.verifyProof upperBound vCommit proof


