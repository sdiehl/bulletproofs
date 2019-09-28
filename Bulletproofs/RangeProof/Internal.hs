{-# LANGUAGE DeriveGeneric, DeriveAnyClass, ViewPatterns #-}
module Bulletproofs.RangeProof.Internal where

import Protolude

import Numeric (showIntAtBase)
import Data.Char (intToDigit, digitToInt)

import Control.Monad.Random (MonadRandom)
import Data.Field.Galois (PrimeField(..))
import Data.Curve.Weierstrass.SECP256K1 (PA, Fr, mul, inv, gen)
import Bulletproofs.Utils
import Bulletproofs.InnerProductProof.Internal

data RangeProof f p
  = RangeProof
    { tBlinding :: f
    -- ^ Blinding factor of the T1 and T2 commitments,
    -- combined into the form required to make the committed version of the x-polynomial add up
    , mu :: f
    -- ^ Blinding factor required for the Verifier to verify commitments A, S
    , t :: f
    -- ^ Dot product of vectors l and r that prove knowledge of the value in range
    -- t = t(x) = l(x) · r(x)
    , aCommit :: p
    -- ^ Commitment to aL and aR, where aL and aR are vectors of bits
    -- such that aL · 2^n = v and aR = aL − 1^n .
    -- A = α · H + aL · G + aR · H
    , sCommit :: p
    -- ^ Commitment to new vectors sL, sR, created at random by the Prover
    , t1Commit :: p
    -- ^ Pedersen commitment to coefficient t1
    , t2Commit :: p
    -- ^ Pedersen commitment to coefficient t2
    , productProof :: InnerProductProof f p
    -- ^ Inner product argument to prove that a commitment P
    -- has vectors l, r ∈  Z^n for which P = l · G + r · H + ( l, r ) · U
    } deriving (Show, Eq, Generic, NFData)

data RangeProofError f
  = UpperBoundTooLarge Integer  -- ^ The upper bound of the range is too large
  | ValueNotInRange f     -- ^ Value is not within the range required
  | ValuesNotInRange [f]  -- ^ Values are not within the range required
  | NNotPowerOf2 Integer        -- ^ Dimension n is required to be a power of 2
  deriving (Show, Eq, Generic, NFData)

-----------------------------
-- Polynomials
-----------------------------

data LRPolys f
  = LRPolys
    { l0 :: [f]
    , l1 :: [f]
    , r0 :: [f]
    , r1 :: [f]
    }

data TPoly f
  = TPoly
    { t0 :: f
    , t1 :: f
    , t2 :: f
    }

-----------------------------
-- Internal functions
-----------------------------

-- | Encode the value v into a bit representation. Let aL be a vector
-- of bits such that <aL, 2^n> = v (put more simply, the components of a L are the
-- binary digits of v).
encodeBit :: Integer -> Fr -> [Fr]
encodeBit n v = fillWithZeros n $ fromIntegral . digitToInt <$> showIntAtBase 2 intToDigit (fromP v) ""

-- | Bits of v reversed.
-- v = <a, 2^n> = a_0 * 2^0 + ... + a_n-1 * 2^(n-1)
reversedEncodeBit :: Integer -> Fr -> [Fr]
reversedEncodeBit n = reverse . encodeBit n

reversedEncodeBitMulti :: Integer -> [Fr] -> [Fr]
reversedEncodeBitMulti n = foldl' (\acc v -> acc ++ reversedEncodeBit n v) []

-- | In order to prove that v is in range, each element of aL is either 0 or 1.
-- We construct a “complementary” vector aR = aL − 1^n and require that
-- aL ◦ aR = 0 hold.
complementaryVector :: Num a => [a] -> [a]
complementaryVector aL = (\vi -> vi - 1) <$> aL


-- | Add non-relevant zeros to a vector to match the size
-- of the other vectors used in the protocol
fillWithZeros :: Num f => Integer -> [f] -> [f]
fillWithZeros n aL = zeros ++ aL
  where
    zeros = replicate (fromInteger n - length aL) 0

-- | Obfuscate encoded bits with challenges y and z.
-- z^2 * <aL, 2^n> + z * <aL − 1^n − aR, y^n> + <aL, aR · y^n> = (z^2) * v
-- The property holds because <aL − 1^n − aR, y^n> = 0 and <aL · aR,  y^n> = 0
obfuscateEncodedBits :: Integer -> [Fr] -> [Fr] -> Fr -> Fr -> Fr
obfuscateEncodedBits n aL aR y z
  = ((z ^ 2) * dot aL (powerVector 2 n))
    + (z * dot ((aL ^-^ powerVector 1 n) ^-^ aR) yN)
    + dot (hadamard aL aR) yN
  where
    yN = powerVector y n

-- Convert obfuscateEncodedBits into a single inner product.
-- We can afford for this factorization to leave terms “dangling”, but
-- what’s important is that the aL , aR terms be kept inside
-- (since they can’t be shared with the Verifier):
-- <aL − z * 1^n , y^n ◦ (aR + z * 1^n) + z^2 * 2^n> = z 2 v + δ(y, z)
obfuscateEncodedBitsSingle :: Integer -> [Fr] -> [Fr] -> Fr -> Fr -> Fr
obfuscateEncodedBitsSingle n aL aR y z
  = dot
      (aL ^-^ z1n)
      (hadamard (powerVector y n) (aR ^+^ z1n) ^+^ ((*) (z ^ 2) <$> powerVector 2 n))
  where
    z1n = (*) z <$> powerVector 1 n

-- | We need to blind the vectors aL, aR to make the proof zero knowledge.
-- The Prover creates randomly vectors sL and sR. On creating these, the
-- Prover can send commitments to these vectors;
-- these are properly blinded vector Pedersen commitments:
commitBitVectors
  :: (MonadRandom m)
  => Fr
  -> Fr
  -> [Fr]
  -> [Fr]
  -> [Fr]
  -> [Fr]
  -> m (PA, PA)
commitBitVectors aBlinding sBlinding aL aR sL sR = do
    let aLG = sumExps aL gs
        aRH = sumExps aR hs
        sLG = sumExps sL gs
        sRH = sumExps sR hs
        aBlindingH = mul h aBlinding
        sBlindingH = mul h sBlinding

    -- Commitment to aL and aR
    let aCommit = aBlindingH <> aLG <> aRH

    -- Commitment to sL and sR
    let sCommit = sBlindingH <> sLG <> sRH

    pure (aCommit, sCommit)

-- | (z − z^2) * <1^n, y^n> − z^3 * <1^n, 2^n>
delta :: Integer -> Integer -> Fr -> Fr -> Fr
delta n m y z
  = ((z - (z ^ 2)) * dot (powerVector 1 nm) (powerVector y nm))
  - foldl' (\acc j -> acc + ((z ^ (j + 2)) * dot (powerVector 1 n) (powerVector 2 n))) 0 [1..m]
  where
    nm = n * m

-- | Check that a value is in a specific range
checkRange :: Integer -> Fr -> Bool
checkRange n (fromP -> v) = v >= 0 && v < 2 ^ n

-- | Check that a value is in a specific range
checkRanges :: Integer -> [Fr] -> Bool
checkRanges n vs = and $ fmap (\(fromP -> v) -> v >= 0 && v < 2 ^ n) vs

-- | Compute commitment of linear vector polynomials l and r
-- P = A + xS − zG + (z*y^n + z^2 * 2^n) * hs'
computeLRCommitment
  :: Integer
  -> Integer
  -> PA
  -> PA
  -> Fr
  -> Fr
  -> Fr
  -> Fr
  -> Fr
  -> Fr
  -> [PA]
  -> PA
computeLRCommitment n m aCommit sCommit t tBlinding mu x y z hs'
  = aCommit                                               -- A
    <>
    (sCommit `mul` x)                                    -- xS
    <>
    (inv (gsSum `mul` z))             -- (- zG)
    <>
    sumExps hExp hs'     -- (hExp Hs')
    <>
    foldl'
      (\acc j -> acc <> sumExps (hExp' j) (sliceHs' j))
      mempty
      [1..m]
    <>
    (inv (h `mul` mu))
    <>
    (u `mul` t)
    where
      gsSum = foldl' (<>) mempty (take (fromIntegral nm) gs)
      hExp = (*) z <$> powerVector y nm
      hExp' j = (*) (z ^ (j+1)) <$> powerVector 2 n
      sliceHs' j = slice n j hs'
      uChallenge = shamirU tBlinding mu t
      u = gen `mul` uChallenge
      nm = n * m
