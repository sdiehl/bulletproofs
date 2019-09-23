{-# LANGUAGE RecordWildCards, ScopedTypeVariables, ViewPatterns, TypeApplications #-}
module Bulletproofs.ArithmeticCircuit.Prover where

import Protolude

import Control.Monad.Random (MonadRandom, getRandomR)

import Data.Curve.Weierstrass.SECP256K1 (PA, Fr, _r)
import Data.Curve.Weierstrass

import Bulletproofs.Utils hiding (shamirZ)
import qualified Bulletproofs.InnerProductProof as IPP
import Bulletproofs.ArithmeticCircuit.Internal

-- | Generate a zero-knowledge proof of computation
-- for an arithmetic circuit with a valid witness
generateProof
  :: forall m . (MonadRandom m)
  => ArithCircuit Fr
  -> ArithWitness Fr
  -> m (ArithCircuitProof Fr PA)
generateProof (padCircuit -> ArithCircuit{..}) ArithWitness{..} = do
  let GateWeights{..} = weights
      Assignment{..} = padAssignment assignment
      genBlinding = (fromInteger :: Integer -> Fr) <$> getRandomR (1, fromIntegral _r - 1)
  aiBlinding <- genBlinding
  aoBlinding <- genBlinding
  sBlinding <- genBlinding
  let n = fromIntegral $ length aL
      aiCommit = commitBitVector aiBlinding aL aR  -- commitment to aL, aR
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
      (lPoly, rPoly) = computePolynomials n aL aR aO sL sR y zwL zwR zwO
      tPoly = multiplyPoly lPoly rPoly

      w = (aL `vectorMatrixProductT` wL)
        ^+^ (aR `vectorMatrixProductT` wR)
        ^+^ (aO `vectorMatrixProductT` wO)

      _t2 = (aL `dot` (aR `hadamard` ys))
         - (aO `dot` ys)
         + (zs `dot` w)
         + delta n y zwL zwR

  tBlindings <- insertAt 2 0 . (:) 0 <$> replicateM 5 ((fromInteger @Fr) <$> getRandomR (1, fromIntegral _r - 1))
  let tCommits = zipWith commit tPoly tBlindings

  let x = shamirGs tCommits
      _evalTCommit = sumExps (powerVector x 7) tCommits

  let ls = evaluatePolynomial n lPoly x
      rs = evaluatePolynomial n rPoly x
      t = ls `dot` rs

      commitTimesWeigths = commitBlinders `vectorMatrixProductT` commitmentWeights
      zGamma = zs `dot` commitTimesWeigths
      tBlinding = sum (zipWith (\i blinding -> blinding * (x ^ i)) [0..] tBlindings)
                + ((x ^ 2) * zGamma)

      mu = aiBlinding * x + aoBlinding * (x ^ 2) + sBlinding * (x ^ 3)

  let uChallenge = shamirU tBlinding mu t
      u = gen `mul` uChallenge
      hs' = zipWith mul hs (powerVector (recip y) n)
      gExp = (*) x <$> (powerVector (recip y) n `hadamard` zwR)
      hExp = (((*) x <$> zwL) ^+^ zwO) ^-^ ys
      commitmentLR = (aiCommit `mul` x)
                   `add` (aoCommit `mul` (x ^ 2))
                   `add` (sCommit `mul` (x ^ 3))
                   `add` sumExps gExp gs
                   `add` sumExps hExp hs'
                   `add` (inv (h `mul` mu))
                   `add` (u `mul` t)

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
    qLen = fromIntegral $ length commitmentWeights
    computePolynomials n aL aR aO sL sR y zwL zwR zwO
      = ( [l0, l1, l2, l3]
        , [r0, r1, r2, r3]
        )
      where
        l0 = replicate (fromIntegral n) 0
        l1 = aL ^+^ (powerVector (recip y) n `hadamard` zwR)
        l2 = aO
        l3 = sL

        r0 = zwO ^-^ powerVector y n
        r1 = (powerVector y n `hadamard` aR) ^+^ zwL
        r2 = replicate (fromIntegral n) 0
        r3 = powerVector y n `hadamard` sR

