module Bulletproofs.Utils where

import Protolude

import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto
import Crypto.Random (MonadRandom)
import Crypto.Number.Generate (generateMax)

import Bulletproofs.Fq as Fq hiding (asInteger)
import Bulletproofs.Curve

class AsInteger a where
  asInteger :: a -> Integer

instance AsInteger Fq where
  asInteger (Fq x) = x

instance AsInteger Integer where
  asInteger x = x

-- Class for specialisations of field operations that may have
-- optimised implementations.
class (Num f, Fractional f) => Field f where
  fSquare :: f -> f

instance Field Fq where
  fSquare = Fq.fqSquare

-- | Return a vector containing the first n powers of a
powerVector :: (Eq f, Num f) => f -> Integer -> [f]
powerVector a x
  = (\i -> if i == 0 && a == 0 then 0 else a ^ i) <$> [0..x-1]

-- | Hadamard product or entry wise multiplication of two vectors
hadamardp :: Num a => [a] -> [a] -> [a]
hadamardp a b | length a == length b = zipWith (*) a b
              | otherwise = panic "Vector sizes must match"

dot :: Num a => [a] -> [a] -> a
dot xs ys = sum $ hadamardp xs ys

(^+^) :: Num a => [a] -> [a] -> [a]
(^+^) = zipWith (+)

(^-^) :: Num a => [a] -> [a] -> [a]
(^-^) = zipWith (-)

-- | Add two points of the same curve
addP :: Crypto.Point -> Crypto.Point -> Crypto.Point
addP = Crypto.pointAdd curve

-- | Substract two points of the same curve
subP :: Crypto.Point -> Crypto.Point -> Crypto.Point
subP x y = Crypto.pointAdd curve x (Crypto.pointNegate curve y)

-- | Multiply a scalar and a point in an elliptic curve
mulP :: AsInteger f => f -> Crypto.Point -> Crypto.Point
mulP x = Crypto.pointMul curve (asInteger x)

-- | Double exponentiation (Shamir's trick): g0^x0 + g1^x1
addTwoMulP :: AsInteger f => f -> Crypto.Point -> f -> Crypto.Point -> Crypto.Point
addTwoMulP exp0 pt0 exp1 pt1 = Crypto.pointAddTwoMuls curve (asInteger exp0) pt0 (asInteger exp1) pt1

-- | Raise every point to the corresponding exponent, sum up results
sumExps :: AsInteger f => [f] -> [Crypto.Point] -> Crypto.Point
sumExps (exp0:exp1:exps) (pt0:pt1:pts)
  = addTwoMulP exp0 pt0 exp1 pt1 `addP` sumExps exps pts
sumExps (exp:_) (pt:_) = mulP exp pt -- this also catches cases where either list is longer than the other
sumExps _ _ = Crypto.PointO  -- this catches cases where either list is empty

-- | Create a Pedersen commitment to a value given
-- a value and a blinding factor
commit :: AsInteger f => f -> f -> Crypto.Point
commit x r = addTwoMulP x g r h

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
randomN n = generateMax (2^n)

chooseBlindingVectors :: (Num f, MonadRandom m) => Integer -> m ([f], [f])
chooseBlindingVectors n = do
  sL <- replicateM (fromInteger n) (fromInteger <$> generateMax (2^n))
  sR <- replicateM (fromInteger n) (fromInteger <$> generateMax (2^n))
  pure (sL, sR)

--------------------------------------------------
-- Fiat-Shamir transformations
--------------------------------------------------

shamirY :: Num f => Crypto.Point -> Crypto.Point -> f
shamirY aCommit sCommit
  = fromInteger $ oracle $
      show q <> pointToBS aCommit <> pointToBS sCommit

shamirZ :: (Show f, Num f) => Crypto.Point -> Crypto.Point -> f -> f
shamirZ aCommit sCommit y
  = fromInteger $ oracle $
      show q <> pointToBS aCommit <> pointToBS sCommit <> show y

shamirX
  :: (Show f, Num f)
  => Crypto.Point
  -> Crypto.Point
  -> Crypto.Point
  -> Crypto.Point
  -> f
  -> f
  -> f
shamirX aCommit sCommit t1Commit t2Commit y z
  = fromInteger $ oracle $
      show q <> pointToBS aCommit <> pointToBS sCommit <> pointToBS t1Commit <> pointToBS t2Commit <> show y <> show z

shamirX'
  :: Num f
  => Crypto.Point
  -> Crypto.Point
  -> Crypto.Point
  -> f
shamirX' commitmentLR l' r'
  = fromInteger $ oracle $
      show q <> pointToBS l' <> pointToBS r' <> pointToBS commitmentLR

shamirU :: (Show f, Num f) => f -> f -> f -> f
shamirU tBlinding mu t
  = fromInteger $ oracle $
      show q <> show tBlinding <> show mu <> show t
