{-# LANGUAGE NamedFieldPuns, MultiWayIf #-}

module Bulletproofs.InnerProductProof.Prover (
  generateProof,
) where

import Protolude

import Control.Exception (assert)
import Data.Curve.Weierstrass.SECP256K1 (PA, Fr)
import Data.Curve.Weierstrass hiding (char)

import Bulletproofs.Utils
import Bulletproofs.InnerProductProof.Internal

-- | Generate proof that a witness l, r satisfies the inner product relation
-- on public input (Gs, Hs, h)
generateProof
  :: InnerProductBase PA   -- ^ Generators Gs, Hs, h
  -> PA
  -- ^ Commitment P = A + xS − zG + (z*y^n + z^2 * 2^n) * hs' of vectors l and r
  -- whose inner product is t
  -> InnerProductWitness Fr
  -- ^ Vectors l and r that hide bit vectors aL and aR, respectively
  -> InnerProductProof Fr PA
generateProof productBase commitmentLR witness
  = generateProof' productBase commitmentLR witness [] []

generateProof'
  :: InnerProductBase PA
  -> PA
  -> InnerProductWitness Fr
  -> [PA]
  -> [PA]
  -> InnerProductProof Fr PA
generateProof'
  InnerProductBase{ bGs, bHs, bH }
  commitmentLR
  InnerProductWitness{ ls, rs }
  lCommits
  rCommits
  = case (ls, rs) of
    ([], [])   -> InnerProductProof [] [] 0 0
    ([l], [r]) -> InnerProductProof (reverse lCommits) (reverse rCommits) l r
    _          -> assert (checkLGs && checkRHs && checkLBs && checkC && checkC')
                $ generateProof'
                    InnerProductBase { bGs = gs'', bHs = hs'', bH = bH }
                    commitmentLR'
                    InnerProductWitness { ls = ls', rs = rs' }
                    (lCommit:lCommits)
                    (rCommit:rCommits)
  where
    n' = fromIntegral $ length ls
    nPrime = n' `div` 2

    (lsLeft, lsRight) = splitAt nPrime ls
    (rsLeft, rsRight) = splitAt nPrime rs
    (gsLeft, gsRight) = splitAt nPrime bGs
    (hsLeft, hsRight) = splitAt nPrime bHs

    cL = dot lsLeft rsRight
    cR = dot lsRight rsLeft

    lCommit = sumExps lsLeft gsRight
         `add`
         sumExps rsRight hsLeft
         `add`
         (bH `mul` cL)

    rCommit = sumExps lsRight gsLeft
         `add`
         sumExps rsLeft hsRight
         `add`
         (bH `mul` cR)

    x = shamirX' commitmentLR lCommit rCommit

    xInv = recip x
    xs = replicate nPrime x
    xsInv = replicate nPrime xInv

    gs'' = zipWith (\(exp0, pt0) (exp1, pt1) -> addTwoMulP exp0 pt0 exp1 pt1) (zip xsInv gsLeft) (zip xs gsRight)
    hs'' = zipWith (\(exp0, pt0) (exp1, pt1) -> addTwoMulP exp0 pt0 exp1 pt1) (zip xs hsLeft) (zip xsInv hsRight)

    ls' = ((*) x <$> lsLeft) ^+^ ((*) xInv <$> lsRight)
    rs' = ((*) xInv <$> rsLeft) ^+^ ((*) x <$> rsRight)

    commitmentLR'
      = (lCommit `mul` (x ^ 2))
        `add`
        (rCommit `mul` (xInv ^ 2))
        `add`
        commitmentLR

    -----------------------------
    -- Checks
    -----------------------------

    aL' = sumExps lsLeft gsRight
    aR' = sumExps lsRight gsLeft

    bL' = sumExps rsLeft hsRight
    bR' = sumExps rsRight hsLeft

    z = dot ls rs
    z' = dot ls' rs'

    lGs = sumExps ls bGs
    rHs = sumExps rs bHs

    lGs' = sumExps ls' gs''
    rHs' = sumExps rs' hs''

    checkLGs
      = lGs'
        ==
        sumExps ls bGs
        `add`
        (aL' `mul` (x ^ 2))
        `add`
        (aR' `mul` (xInv ^ 2))

    checkRHs
      = rHs'
        ==
        sumExps rs bHs
        `add`
        (bR' `mul` (x ^ 2))
        `add`
        (bL' `mul` (xInv ^ 2))

    checkLBs
      = dot ls' rs'
        ==
        dot ls rs + (x ^ 2) * cL + (xInv ^ 2) * cR

    checkC
      = commitmentLR
        ==
        (bH `mul` z)
        `add`
        lGs
        `add`
        rHs

    checkC'
      = commitmentLR'
        ==
        (bH `mul` z')
        `add`
        lGs'
        `add`
        rHs'
