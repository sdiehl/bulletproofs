{-# LANGUAGE TypeFamilies #-}
-- | Prime field with characteristic _q, over which the elliptic curve
-- is defined and the other finite field extensions.
--
--   * Fq
--   * Fq2 := Fq[u]/u^2 + 1
--   * Fq6 := Fq2[v]/v^3 - (9 + u)
--   * Fq12 := Fq6[w]/w^2 - v

module Bulletproofs.Fq
  ( Fq
  , PF
  , fqRandom
  , fqPow
  , fqSqrt
  , toInt
  ) where

import Protolude

import Crypto.Random (MonadRandom)
import Crypto.Number.Generate (generateMax)
import Math.NumberTheory.Moduli.Class (powMod)
import PrimeField (PrimeField(..), toInt)
import Pairing.Modular
import Bulletproofs.Curve


-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

-- | Prime field @Fq@ with characteristic @_q@
type Fq = PrimeField 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

-- | Type family to extract the characteristic of the prime field
type family PF a where
  PF (PrimeField k) = k

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Ord Fq where
  compare = on compare toInt

-------------------------------------------------------------------------------
-- Random
-------------------------------------------------------------------------------

fqRandom :: MonadRandom m => m Fq
fqRandom = fromInteger <$> generateMax _q

-------------------------------------------------------------------------------
-- Y for X
-------------------------------------------------------------------------------

fqPow :: Integral e => Fq -> e -> Fq
fqPow a b = fromInteger (withQ (modUnOp (toInt a) (flip powMod b)))
{-# INLINE fqPow #-}

fqSqrt :: Bool -> Fq -> Maybe Fq
fqSqrt largestY a = do
  (y1, y2) <- withQM (modUnOpMTup (toInt a) bothSqrtOf)
  return (fromInteger ((if largestY then max else min) y1 y2))

fqYforX :: Fq -> Bool -> Maybe Fq
fqYforX x largestY = fqSqrt largestY (x `fqPow` 3 + fromInteger _b)
