{-# LANGUAGE TypeFamilies #-}
module Bulletproofs.Curve (
  Fq,
  PF,
  _q,
  _a,
  _b,
  g,
  h,
  gs,
  hs,
  curve,
  oracle,
  pointToBS,
) where

import Protolude hiding (hash)
import Data.Maybe (fromJust)

import Crypto.Hash
import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto

import qualified Data.ByteArray as BA
import Crypto.Number.Serialize (os2ip)
import Data.Field.Galois (Prime)
import Math.NumberTheory.Moduli.Sqrt (sqrtsModPrime)
import Math.NumberTheory.UniqueFactorisation (isPrime)

-- Implementation using the elliptic curve secp256k12
-- which has 128 bit security.
-- Parameters as in Cryptonite:
-- SEC_p256k1 = CurveFP  $ CurvePrime
--     0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
--     (CurveCommon
--         { ecc_a = 0x0000000000000000000000000000000000000000000000000000000000000000
--         , ecc_b = 0x0000000000000000000000000000000000000000000000000000000000000007
--         , ecc_g = Point 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
--                         0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
--         , ecc_n = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
--         , ecc_h = 1
--         })


-- | Prime field @Fq@ with characteristic @_q@
type Fq = Prime 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141


-- | Type family to extract the characteristic of the prime field
type family PF a where
  PF (Prime k) = k

curveName :: Crypto.CurveName
curveName = Crypto.SEC_p256k1

curve :: Crypto.Curve
curve = Crypto.getCurveByName curveName

-- | Order of the curve
_q :: Integer
_q = Crypto.ecc_n . Crypto.common_curve $ curve

_b :: Integer
_b = Crypto.ecc_b . Crypto.common_curve $ curve

_a :: Integer
_a = Crypto.ecc_a . Crypto.common_curve $ curve

-- | Generator of the curve
g :: Crypto.Point
g = Crypto.ecc_g $ Crypto.common_curve curve

-- | H = aG where a is not known
h :: Crypto.Point
h = generateH g ""

-- | Generate vector of generators in a deterministic way from the curve generator g
-- by applying H(encode(g) || i) where H is a secure hash function
gs :: [Crypto.Point]
gs = Crypto.pointBaseMul curve . oracle . (<> pointToBS g) . show <$> [1..]

-- | Generate vector of generators in a deterministic way from the curve generator h
-- by applying H(encode(h) || i) where H is a secure hash function
hs :: [Crypto.Point]
hs = Crypto.pointBaseMul curve . oracle . (<> pointToBS h) . show <$> [1..]

-- | A random oracle. In the Fiat-Shamir heuristic, its input
-- is specifically the transcript of the interaction up to that point.
oracle :: ByteString -> Integer
oracle x = os2ip (sha256 x)

sha256 :: ByteString -> ByteString
sha256 bs = BA.convert (hash bs :: Digest SHA3_256)

pointToBS :: Crypto.Point -> ByteString
pointToBS Crypto.PointO      = ""
pointToBS (Crypto.Point x y) = show x <> show y

-- | Characteristic of the underlying finite field of the elliptic curve
_p :: Integer
_p = Crypto.ecc_p cp
  where
    cp = case curve of
      Crypto.CurveFP c -> c
      Crypto.CurveF2m _ -> panic "Not a FP curve"

-- | Iterative algorithm to generate H.
-- The important thing about the H value is that nobody gets
-- to know its discrete logarithm "k" such that H = kG
generateH :: Crypto.Point -> [Char] -> Crypto.Point
generateH basePoint extra =
  case yM of
    [] -> generateH basePoint (toS $ '1':extra)
    (y:_) -> if Crypto.isPointValid curve (Crypto.Point x y)
      then Crypto.Point x y
      else generateH basePoint (toS $ '1':extra)
  where
    x = oracle (pointToBS basePoint <> toS extra) `mod` _p
    yM = sqrtsModPrime (fromInteger (x ^ 3 + 7)) ((fromJust (isPrime _p)))
