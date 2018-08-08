{-# LANGUAGE RecordWildCards, ScopedTypeVariables #-}
module Bulletproofs.ArithmeticCircuit.Prover where

import Protolude

import Crypto.Random.Types (MonadRandom(..))
import Crypto.Number.Generate (generateMax)
import qualified Crypto.PubKey.ECC.Generate as Crypto
import qualified Crypto.PubKey.ECC.Prim as Crypto
import qualified Crypto.PubKey.ECC.Types as Crypto

import Linear.Vector ((^+^), (^-^))
import Linear.Metric (dot)

import Bulletproofs.Curve
import Bulletproofs.Utils hiding (shamirZ)
import Bulletproofs.RangeProof.Internal hiding (delta)
import qualified Bulletproofs.InnerProductProof as IPP
import Bulletproofs.ArithmeticCircuit.Internal

generateProof
  :: forall f m
   . (MonadRandom m, AsInteger f, Field f, Show f, Eq f)
  => ArithCircuit f
  -> ArithWitness f
  -> m (ArithCircuitProof f)
generateProof ArithCircuit{..} ArithWitness{..} = do
  let GateWeights{..} = weights
  let Assignment{..} = inputs
  [aiBlinding, aoBlinding, sBlinding] <- replicateM 3 ((fromInteger :: Integer -> f) <$> generateMax (2^n))

  let aiCommit = commitBitVector aiBlinding aL aR  -- commitment to aL, aR
      aoCommit = commitBitVector aoBlinding aO []  -- commitment to aO

  (sL, sR) <- chooseBlindingVectors n              -- choose blinding vectors sL, sR
  let sCommit = commitBitVector sBlinding sL sR    -- commitment to sL, sR

  let y = shamirGxGxG aiCommit aoCommit sCommit
      z = shamirZ y
      ys = powerVector y n
      zs = drop 1 (powerVector z (qLen + 1))

      zwL = zs `vectorMatrixProduct` wL
      zwR = zs `vectorMatrixProduct` wR
      zwO = zs `vectorMatrixProduct` wO

      -- Polynomials
      [lPoly, rPoly] = computePolynomials aL aR aO sL sR y z zwL zwR zwO
      tPoly = multiplyPoly lPoly rPoly

      w = (aL `vectorMatrixProductT` wL)
        ^+^ (aR `vectorMatrixProductT` wR)
        ^+^ (aO `vectorMatrixProductT` wO)

      t2 = (aL `dot` (aR `hadamardp` ys))
         - (aO `dot` ys)
         + (zs `dot` w)
         + delta n y zwL zwR

  tBlindings <- insertAt 2 0 . (:) 0 <$> replicateM 5 ((fromInteger :: Integer -> f) <$> generateMax (2^n))
  let tCommits = zipWith commit tPoly tBlindings

  let x = shamirGs tCommits
      evalTCommit = foldl' addP Crypto.PointO (zipWith mulP (powerVector x 7) tCommits)

  let ls = evaluatePolynomial n lPoly x
      rs = evaluatePolynomial n rPoly x
      t = ls `dot` rs

      commitTimesWeigths = commitBlinders `vectorMatrixProductT` commitmentWeights
      zGamma = zs `dot` commitTimesWeigths
      tBlinding = sum (zipWith (\i blinding -> blinding * (x ^ i)) [0..] tBlindings)
                + (fSquare x * zGamma)

      mu = aiBlinding * x + aoBlinding * fSquare x + sBlinding * (x ^ 3)

  let uChallenge = shamirU tBlinding mu t
      u = uChallenge `mulP` g
      hs' = zipWith mulP (powerVector (recip y) n) hs
      gExp = (*) x <$> (powerVector (recip y) n `hadamardp` zwR)
      hExp = (((*) x <$> zwL) ^+^ zwO) ^-^ ys
      commitmentLR = (x `mulP` aiCommit)
                   `addP` (fSquare x `mulP` aoCommit)
                   `addP` ((x ^ 3)`mulP` sCommit)
                   `addP` foldl' addP Crypto.PointO (zipWith mulP gExp gs)
                   `addP` foldl' addP Crypto.PointO (zipWith mulP hExp hs')
                   `addP` Crypto.pointNegate curve (mu `mulP` h)
                   `addP` (t `mulP` u)

  let productProof = IPP.generateProof
                        IPP.InnerProductBase { bGs = gs, bHs = hs', bH = u }
                        commitmentLR
                        IPP.InnerProductWitness { ls = ls, rs = rs }

  pure ArithCircuitProof
      { tBlinding = tBlinding
      , mu = mu
      , t = t
      , aiCommit = aiCommit
      , aoCommit = aoCommit
      , sCommit = sCommit
      , tCommits = tCommits
      , productProof = productProof
      }
  where
    n = fromIntegral $ length (aL inputs) -- # multiplication gates
    qLen = fromIntegral $ length commitmentWeights
    removeSnd vs = take 1 vs ++ drop 2 vs

    computePolynomials aL aR aO sL sR y z zwL zwR zwO
      = [ [l0, l1, l2, l3]
        , [r0, r1, r2, r3]
        ]
      where
        l0 = replicate (fromIntegral n) 0
        l1 = aL ^+^ (powerVector (recip y) n `hadamardp` zwR)
        l2 = aO
        l3 = sL

        r0 = zwO ^-^ powerVector y n
        r1 = (powerVector y n `hadamardp` aR) ^+^ zwL
        r2 = replicate (fromIntegral n) 0
        r3 = powerVector y n `hadamardp` sR

