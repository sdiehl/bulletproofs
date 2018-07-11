module Bulletproofs.Utils where

import Protolude

import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto

import Bulletproofs.Fq as Fq
import Bulletproofs.Curve

-- | Return a vector containing the first n powers of a
powerVector :: Fq -> Integer -> [Fq]
powerVector (Fq a) x = (\i -> Fq.new (a ^ i)) <$> [0..x-1]

-- | Inner product between two vector polynomials
dotp :: Num a => [a] -> [a] -> a
dotp a b = foldl' (+) 0 (hadamardp a b)

-- | Hadamard product or entry wise multiplication of two vectors
hadamardp :: Num a => [a] -> [a] -> [a]
hadamardp a b | length a == length b = zipWith (*) a b
              | otherwise = panic "Vector sizes must match"

-- | Add two points of the same curve
addP :: Crypto.Point -> Crypto.Point -> Crypto.Point
addP = Crypto.pointAdd curve

-- | Substract two points of the same curve
subP :: Crypto.Point -> Crypto.Point -> Crypto.Point
subP x y = Crypto.pointAdd curve x (Crypto.pointNegate curve y)

-- | Multiply a scalar and a point in an elliptic curve
mulP :: Fq -> Crypto.Point -> Crypto.Point
mulP (Fq x) = Crypto.pointMul curve x

-- | Create a Pedersen commitment to a value given
-- a value and a blinding factor
commit :: Fq -> Fq -> Crypto.Point
commit x r = (x `mulP` g) `addP` (r `mulP` h)

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

--------------------------------------------------
-- Fiat-Shamir transformations
--------------------------------------------------

shamirY :: Crypto.Point -> Crypto.Point -> Fq
shamirY aCommit sCommit
  = Fq.new $ oracle $
      show q <> pointToBS aCommit <> pointToBS sCommit

shamirZ :: Crypto.Point -> Crypto.Point -> Fq -> Fq
shamirZ aCommit sCommit y
  = Fq.new $ oracle $
      show q <> pointToBS aCommit <> pointToBS sCommit <> show y

shamirX
  :: Crypto.Point
  -> Crypto.Point
  -> Crypto.Point
  -> Crypto.Point
  -> Fq
  -> Fq
  -> Fq
shamirX aCommit sCommit t1Commit t2Commit y z
  = Fq.new $ oracle $
      show q <> pointToBS aCommit <> pointToBS sCommit <> pointToBS t1Commit <> pointToBS t2Commit <> show y <> show z

shamirX'
  :: Crypto.Point
  -> Crypto.Point
  -> Crypto.Point
  -> Fq
shamirX' commitmentLR l' r'
  = Fq.new $ oracle $
      show q <> pointToBS l' <> pointToBS r' <> pointToBS commitmentLR

shamirU :: Fq -> Fq -> Fq -> Fq
shamirU tBlinding mu t
  = Fq.new $ oracle $
      show q <> show tBlinding <> show mu <> show t
