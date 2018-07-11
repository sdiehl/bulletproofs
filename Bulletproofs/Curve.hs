module Bulletproofs.Curve (
  q,
  g,
  h,
  gs,
  hs,
  curve,
  oracle,
  pointToBS,
) where

import Protolude hiding (hash)

import Crypto.Hash
import qualified Crypto.PubKey.ECC.Generate as Crypto
import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto

import qualified Data.ByteArray as BA
import Crypto.Number.Serialize (os2ip)
import Math.NumberTheory.Moduli.Sqrt (sqrtModP)

import Numeric
import qualified Data.List as L

curveName :: Crypto.CurveName
curveName = Crypto.SEC_p256k1

curve :: Crypto.Curve
curve = Crypto.getCurveByName curveName

-- | Order of the curve
q :: Integer
q = Crypto.ecc_n . Crypto.common_curve $ curve

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
p :: Integer
p = Crypto.ecc_p cp
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
    Nothing -> generateH basePoint (toS $ '1':extra)
    Just y -> if Crypto.isPointValid curve (Crypto.Point x y)
      then Crypto.Point x y
      else generateH basePoint (toS $ '1':extra)
  where
    x = oracle (pointToBS basePoint <> toS extra) `mod` p
    yM = sqrtModP (x ^ 3 + 7) p

