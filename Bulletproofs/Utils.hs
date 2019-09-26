{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Bulletproofs.Utils where

import Protolude hiding (hash, fromStrict)

import Control.Monad.Random (getRandomR, MonadRandom)
import Data.Field.Galois (PrimeField(..), sr, Prime)
import Data.Curve.Weierstrass.SECP256K1 (PA, SECP256K1, Fq, Fr, _r, gen, def
                                        ,mul, Form(..), Coordinates(..))
import Data.Curve.Weierstrass (Point(..))
import Data.Digest.Pure.SHA (integerDigest, sha256)
import Data.ByteString.Lazy (fromStrict)

type family PF a where
  PF (Prime k) = k

-- | H = aG where a is not known
h :: PA
h = generateH ""

-- | Generate vector of generators in a deterministic way from the curve generator g
-- by applying H(encode(g) || i) where H is a secure hash function
gs :: [PA]
gs = mul gen . (oracle . (<> pointToBS gen) . show) <$> [1..]

-- | Generate vector of generators in a deterministic way from the curve generator h
-- by applying H(encode(h) || i) where H is a secure hash function
hs :: [PA]
hs = mul gen . (oracle . (<> pointToBS h) . show) <$> [1..]

-- | A random oracle. In the Fiat-Shamir heuristic, its input
-- is specifically the transcript of the interaction up to that point.
oracle :: PrimeField f => ByteString -> f
oracle = fromInteger . integerDigest . sha256 . fromStrict

pointToBS :: PA -> ByteString
pointToBS O      = ""
pointToBS (A x y) = show x <> show y

-- | Iterative algorithm to generate H.
-- The important thing about the H value is that nobody gets
-- to know its discrete logarithm "k" such that H = kG
generateH :: [Char] -> PA
generateH extra =
  case yM of
    Nothing -> generateH (toS $ '1':extra)
    Just y -> if def @'Weierstrass @'Affine @SECP256K1 @Fq @Fr (A x y)
      then A x y
      else generateH (toS $ '1':extra)
  where
    x = oracle (pointToBS gen <> toS extra)
    yM = sr (x ^ 3 + 7)

-- | Return a vector containing the first n powers of a
powerVector :: (Eq f, Num f) => f -> Integer -> [f]
powerVector a x
  = (\i -> if i == 0 && a == 0 then 0 else a ^ i) <$> [0..x-1]

-- | Hadamard product or entry wise multiplication of two vectors
hadamard :: Num a => [a] -> [a] -> [a]
hadamard a b | length a == length b = zipWith (*) a b
             | otherwise = panic "Vector sizes must match"

-- | Dot product
dot :: Num a => [a] -> [a] -> a
dot xs ys = sum $ hadamard xs ys

-- | Entry wise sum
(^+^) :: Num a => [a] -> [a] -> [a]
(^+^) = zipWith (+)

-- | Entry wise substraction
(^-^) :: Num a => [a] -> [a] -> [a]
(^-^) = zipWith (-)

-- | Double exponentiation (Shamir's trick): g0^x0 + g1^x1
addTwoMulP :: Fr -> PA -> Fr -> PA -> PA
addTwoMulP exp0 pt0 exp1 pt1 = (pt0 `mul` exp0) <> (pt1 `mul` exp1)

-- | Raise every point to the corresponding exponent, sum up results
sumExps :: [Fr] -> [PA] -> PA
sumExps (exp0:exp1:exps) (pt0:pt1:pts)
  = addTwoMulP exp0 pt0 exp1 pt1 <> sumExps exps pts
sumExps (exp:_) (pt:_) = pt `mul` exp -- this also catches cases where either list is longer than the other
sumExps _ _ = O  -- this catches cases where either list is empty

-- | Create a Pedersen commitment to a value given
-- a value and a blinding factor
commit :: Fr -> Fr -> PA
commit x r = addTwoMulP x gen r h

isLogBase2 :: Integer -> Bool
isLogBase2 x
    | x == 1 = True
    | x == 0 || (x `mod` 2 /= 0) = False
    | otherwise = isLogBase2 (x `div` 2)

logBase2 :: Integer -> Integer
logBase2 = floor . logBase 2.0 . fromIntegral

logBase2M :: Integer -> Maybe Integer
logBase2M x
  = if isLogBase2 x
      then Just (logBase2 x)
      else Nothing

slice :: Integer -> Integer -> [a] -> [a]
slice n j vs = take (fromIntegral $ j  * n - (j - 1)*n) (drop (fromIntegral $ (j - 1) * n) vs)

-- | Append minimal amount of zeroes until the list has a length which
-- is a power of two.
padToNearestPowerOfTwo
  :: Num f => [f] -> [f]
padToNearestPowerOfTwo [] = []
padToNearestPowerOfTwo xs = padToNearestPowerOfTwoOf (length xs) xs

-- | Given n, append zeroes until the list has length 2^n.
padToNearestPowerOfTwoOf
  :: Num f
  => Int -- ^ n
  -> [f] -- ^ list which should have length <= 2^n
  -> [f] -- ^ list which will have length 2^n
padToNearestPowerOfTwoOf i xs = xs ++ replicate padLength 0
  where
    padLength = nearestPowerOfTwo - length xs
    nearestPowerOfTwo = 2 ^ log2Ceil i

-- | Calculate ceiling of log base 2 of an integer.
log2Ceil :: Int -> Int
log2Ceil x = floorLog + correction
  where
    floorLog = finiteBitSize x - 1 - countLeadingZeros x
    correction = if countTrailingZeros x < floorLog
                 then 1
                 else 0

randomN :: MonadRandom m => Integer -> m Integer
randomN n = getRandomR (1, 2^n - 1)

chooseBlindingVectors :: (Num f, MonadRandom m) => Integer -> m ([f], [f])
chooseBlindingVectors n = do
  sL <- replicateM (fromInteger n) (fromInteger <$> getRandomR (1, 2^n - 1))
  sR <- replicateM (fromInteger n) (fromInteger <$> getRandomR (1, 2^n - 1))
  pure (sL, sR)

--------------------------------------------------
-- Fiat-Shamir transformations
--------------------------------------------------

shamirY :: PA -> PA -> Fr
shamirY aCommit sCommit
  = oracle $
      show _r <> pointToBS aCommit <> pointToBS sCommit

shamirZ :: PA -> PA -> Fr -> Fr
shamirZ aCommit sCommit y
  = oracle $
      show _r <> pointToBS aCommit <> pointToBS sCommit <> show y

shamirX
  :: PA
  -> PA
  -> PA
  -> PA
  -> Fr
  -> Fr
  -> Fr
shamirX aCommit sCommit t1Commit t2Commit y z
  = oracle $
      show _r <> pointToBS aCommit <> pointToBS sCommit <> pointToBS t1Commit <> pointToBS t2Commit <> show y <> show z

shamirX' :: PA -> PA -> PA -> Fr
shamirX' commitmentLR l' r'
  = oracle $
      show _r <> pointToBS l' <> pointToBS r' <> pointToBS commitmentLR

shamirU :: Fr -> Fr -> Fr -> Fr
shamirU tBlinding mu t
  = oracle $ show _r <> show tBlinding <> show mu <> show t
