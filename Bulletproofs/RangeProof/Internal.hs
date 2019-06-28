{-# LANGUAGE DeriveGeneric, DeriveAnyClass, ViewPatterns #-}
module Bulletproofs.RangeProof.Internal where

import Protolude

import Numeric (showIntAtBase)
import Data.Char (intToDigit, digitToInt)

import Crypto.Number.Generate (generateMax)
import Crypto.Random.Types (MonadRandom(..))
import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto
import PrimeField (PrimeField(..), toInt)

import Bulletproofs.Utils
import Bulletproofs.Curve
import Bulletproofs.InnerProductProof.Internal

data RangeProof f
  = RangeProof
    { tBlinding :: f
    -- ^ Blinding factor of the T1 and T2 commitments,
    -- combined into the form required to make the committed version of the x-polynomial add up
    , mu :: f
    -- ^ Blinding factor required for the Verifier to verify commitments A, S
    , t :: f
    -- ^ Dot product of vectors l and r that prove knowledge of the value in range
    -- t = t(x) = l(x) · r(x)
    , aCommit :: Crypto.Point
    -- ^ Commitment to aL and aR, where aL and aR are vectors of bits
    -- such that aL · 2^n = v and aR = aL − 1^n .
    -- A = α · H + aL · G + aR · H
    , sCommit :: Crypto.Point
    -- ^ Commitment to new vectors sL, sR, created at random by the Prover
    , t1Commit :: Crypto.Point
    -- ^ Pedersen commitment to coefficient t1
    , t2Commit :: Crypto.Point
    -- ^ Pedersen commitment to coefficient t2
    , productProof :: InnerProductProof f
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
encodeBit :: KnownNat p => Integer -> PrimeField p -> [PrimeField p]
encodeBit n v = fillWithZeros n $ fromIntegral . digitToInt <$> showIntAtBase 2 intToDigit (toInt v) ""

-- | Bits of v reversed.
-- v = <a, 2^n> = a_0 * 2^0 + ... + a_n-1 * 2^(n-1)
reversedEncodeBit :: KnownNat p => Integer -> PrimeField p -> [PrimeField p]
reversedEncodeBit n = reverse . encodeBit n

-- TODO: Test it
reversedEncodeBitMulti :: KnownNat p => Integer -> [PrimeField p] -> [PrimeField p]
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
obfuscateEncodedBits :: KnownNat p => Integer -> [PrimeField p] -> [PrimeField p] -> PrimeField p -> PrimeField p -> PrimeField p
obfuscateEncodedBits n aL aR y z
  = ((z ^ 2) * dot aL (powerVector 2 n))
    + (z * dot ((aL ^-^ powerVector 1 n) ^-^ aR) yN)
    + dot (hadamardp aL aR) yN
  where
    yN = powerVector y n

-- Convert obfuscateEncodedBits into a single inner product.
-- We can afford for this factorization to leave terms “dangling”, but
-- what’s important is that the aL , aR terms be kept inside
-- (since they can’t be shared with the Verifier):
-- <aL − z * 1^n , y^n ◦ (aR + z * 1^n) + z^2 * 2^n> = z 2 v + δ(y, z)
obfuscateEncodedBitsSingle :: KnownNat p => Integer -> [PrimeField p] -> [PrimeField p] -> PrimeField p -> PrimeField p -> PrimeField p
obfuscateEncodedBitsSingle n aL aR y z
  = dot
      (aL ^-^ z1n)
      (hadamardp (powerVector y n) (aR ^+^ z1n) ^+^ ((*) (z ^ 2) <$> powerVector 2 n))
  where
    z1n = (*) z <$> powerVector 1 n

-- | We need to blind the vectors aL, aR to make the proof zero knowledge.
-- The Prover creates randomly vectors sL and sR. On creating these, the
-- Prover can send commitments to these vectors;
-- these are properly blinded vector Pedersen commitments:
commitBitVectors
  :: (MonadRandom m)
  => PrimeField p
  -> PrimeField p
  -> [PrimeField p]
  -> [PrimeField p]
  -> [PrimeField p]
  -> [PrimeField p]
  -> m (Crypto.Point, Crypto.Point)
commitBitVectors aBlinding sBlinding aL aR sL sR = do
    let aLG = sumExps aL gs
        aRH = sumExps aR hs
        sLG = sumExps sL gs
        sRH = sumExps sR hs
        aBlindingH = mulP aBlinding h
        sBlindingH = mulP sBlinding h

    -- Commitment to aL and aR
    let aCommit = aBlindingH `addP` aLG `addP` aRH

    -- Commitment to sL and sR
    let sCommit = sBlindingH `addP` sLG `addP` sRH

    pure (aCommit, sCommit)

-- | (z − z^2) * <1^n, y^n> − z^3 * <1^n, 2^n>
delta :: KnownNat p => Integer -> Integer -> PrimeField p -> PrimeField p -> PrimeField p
delta n m y z
  = ((z - (z ^ 2)) * dot (powerVector 1 nm) (powerVector y nm))
  - foldl' (\acc j -> acc + ((z ^ (j + 2)) * dot (powerVector 1 n) (powerVector 2 n))) 0 [1..m]
  where
    nm = n * m

-- | Check that a value is in a specific range
checkRange :: Integer -> PrimeField p -> Bool
checkRange n (toInt -> v) = v >= 0 && v < 2 ^ n

-- | Check that a value is in a specific range
checkRanges :: Integer -> [PrimeField p] -> Bool
checkRanges n vs = and $ fmap (\(toInt -> v) -> v >= 0 && v < 2 ^ n) vs

-- | Compute commitment of linear vector polynomials l and r
-- P = A + xS − zG + (z*y^n + z^2 * 2^n) * hs'
computeLRCommitment
  :: KnownNat p
  => Integer
  -> Integer
  -> Crypto.Point
  -> Crypto.Point
  -> PrimeField p
  -> PrimeField p
  -> PrimeField p
  -> PrimeField p
  -> PrimeField p
  -> PrimeField p
  -> [Crypto.Point]
  -> Crypto.Point
computeLRCommitment n m aCommit sCommit t tBlinding mu x y z hs'
  = aCommit                                               -- A
    `addP`
    (x `mulP` sCommit)                                    -- xS
    `addP`
    Crypto.pointNegate curve (z `mulP` gsSum)             -- (- zG)
    `addP`
    sumExps hExp hs'     -- (hExp Hs')
    `addP`
    foldl'
      (\acc j -> acc `addP` sumExps (hExp' j) (sliceHs' j))
      Crypto.PointO
      [1..m]
    `addP`
    Crypto.pointNegate curve (mu `mulP` h)
    `addP`
    (t `mulP` u)
    where
      gsSum = foldl' addP Crypto.PointO (take (fromIntegral nm) gs)
      hExp = (*) z <$> powerVector y nm
      hExp' j = (*) (z ^ (j+1)) <$> powerVector 2 n
      sliceHs' j = slice n j hs'
      uChallenge = shamirU tBlinding mu t
      u = uChallenge `mulP` g
      nm = n * m
