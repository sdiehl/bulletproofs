
{-# LANGUAGE ViewPatterns, RecordWildCards  #-}

module TestACProtocol where

import Protolude

import qualified Data.Map as Map
import qualified Data.List as List

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck
import qualified Test.QuickCheck.Monadic as QCM

import Crypto.Number.Generate (generateMax, generateBetween)
import Control.Monad.Random (MonadRandom)

import qualified Bulletproofs.InnerProductProof as IPP
import qualified Bulletproofs.Fq as Fq
import Bulletproofs.Utils
import Bulletproofs.Curve
import Bulletproofs.Fq
import Bulletproofs.ArithmeticCircuit
import Bulletproofs.ArithmeticCircuit.Internal

-- Premises:
-- 1. An arithmetic circuit is determined only by:
--    aL, aR, aO; wL, wR, wO; c
--    such that wL * aL + wR * aR + wO * aO = c
--
-- 2. Prover creates wV and v to
--      - reduce the size of the prove
--      - hide assignment
--    wL * aL + wR * aR + wO * aO - c = wV * v
test_arithCircuitProof_generic :: TestTree
test_arithCircuitProof_generic = localOption (QuickCheckTests 20) $
  testProperty "Arbitrary arithmetic circuit proof" $ QCM.monadicIO $ do
    n <- QCM.run $ (2 ^) <$> generateMax 8
    m <- QCM.run $ generateBetween 1 n
    let q = m

    weights@GateWeights{..} <- QCM.run $ generateGateWeights q n
    commitmentWeights <- QCM.run $ generateWv q m
    Assignment{..} <- QCM.run $ generateRandomAssignment n

    cs <- QCM.run $ replicateM (fromIntegral m) Fq.random
    commitBlinders <- QCM.run $ replicateM (fromIntegral m) Fq.random

    let gateWeights = GateWeights wL wR wO
        gateInputs = Assignment aL aR aO
        vs = computeInputValues weights commitmentWeights gateInputs cs
        commitments = zipWith commit vs commitBlinders
        arithCircuit = ArithCircuit gateWeights commitmentWeights cs
        arithWitness = ArithWitness gateInputs commitments commitBlinders

    proof <- QCM.run $ generateProof arithCircuit arithWitness

    QCM.assert $ verifyProof commitments proof arithCircuit

-- | Test hadamard product relation (paper example)
test_arithCircuitProof_hadamardp :: TestTree
test_arithCircuitProof_hadamardp = localOption (QuickCheckTests 20) $
  testProperty "Arithmetic circuit proof. Hadamard product relation" $ QCM.monadicIO $ do

    let n = 16
    aL <- QCM.run $ replicateM (fromIntegral n) Fq.random
    aR <- QCM.run $ replicateM (fromIntegral n) Fq.random
    let aO = aL `hadamardp` aR

    r <- QCM.run Fq.random
    s <- QCM.run Fq.random
    let v0 = sum aL
        v1 = sum aR

    let v0Commit = commit v0 r
        v1Commit = commit v1 s

    let zeroVector = replicate (fromIntegral n) 0
        oneVector = replicate (fromIntegral n) 1

    let wL = [oneVector, zeroVector]
        wR = [zeroVector, oneVector]
        wO = [zeroVector, zeroVector]

        commitmentWeights = [[1, 0], [0, 1]]
        cs = [0, 0]
        commitments = [v0Commit, v1Commit]
        commitBlinders = [r, s]
        gateWeights = GateWeights wL wR wO
        gateInputs = Assignment aL aR aO
        arithCircuit = ArithCircuit gateWeights commitmentWeights cs
        arithWitness = ArithWitness gateInputs commitments commitBlinders

    proof <- QCM.run $ generateProof arithCircuit arithWitness

    QCM.assert $ verifyProof commitments proof arithCircuit

-- | Test that a basic addition circuit (without multiplication gates) succeeds
-- LINEAR CONSTRAINTS:
-- V[0] + V[1] = V[2]
-- MUL CONSTRAINTS: none
test_arithCircuitProof_add_1 :: TestTree
test_arithCircuitProof_add_1 = localOption (QuickCheckTests 20) $
  testProperty "Arithmetic circuit proof. Basic addition circuit (without multiplication gates)"
    $ QCM.monadicIO $ do
    let n = 0
        m = 3

    commitBlinders <- QCM.run $ replicateM m Fq.random
    let wL = [[]]
        wR = [[]]
        wO = [[]]
        cs = [0]
        aL = []
        aR = []
        aO = []
        commitmentWeights = [[1, 1, -1]]
        vs = [1, 3, 4]
        commitments = zipWith commit vs commitBlinders
        gateWeights = GateWeights wL wR wO
        gateInputs = Assignment aL aR aO
        arithCircuit = ArithCircuit gateWeights commitmentWeights cs
        arithWitness = ArithWitness gateInputs commitments commitBlinders

    proof <- QCM.run $ generateProof arithCircuit arithWitness

    QCM.assert $ verifyProof commitments proof arithCircuit

--  Test that a basic multiplication circuit on inputs (with linear contraints) succeeds
--  LINEAR CONSTRAINTS:
--  a_L[0] = 2
--  a_R[0] = 3
--  a_O[0] = 6
--  MUL CONSTRAINTS (implicit):
--  a_L[0] * a_R[0] = a_O[0]
test_arithCircuitProof_mult_1 :: TestTree
test_arithCircuitProof_mult_1 = localOption (QuickCheckTests 20) $
  testProperty "Arithmetic circuit proof. Basic multiplication circuit on inputs (with linear contraints)"
    $ QCM.monadicIO $ do
    let n = 1
        m = 0

    commitBlinders <- QCM.run $ replicateM m Fq.random
    let wL = [[0], [0], [1]]
        wR = [[0], [1], [0]]
        wO = [[1], [0], [0]]
        cs = [6, 3, 2]
        aL = [2]
        aR = [3]
        aO = [6]
        commitmentWeights = [[], [], []]
        vs = []
        commitments = zipWith commit vs commitBlinders
        gateWeights = GateWeights wL wR wO
        gateInputs = Assignment aL aR aO
        arithCircuit = ArithCircuit gateWeights commitmentWeights cs
        arithWitness = ArithWitness gateInputs commitments commitBlinders


    proof <- QCM.run $ generateProof arithCircuit arithWitness

    QCM.assert $ verifyProof commitments proof arithCircuit

-- Test that a 2 in 2 out shuffle circuit succeeds
-- LINEAR CONSTRAINTS:
-- a_O[0] = a_O[1]
-- a_L[0] = V[0] - z
-- a_L[1] = V[2] - z
-- a_R[0] = V[1] - z
-- a_R[1] = V[3] - z
-- MUL CONSTRAINTS:
-- a_L[0] * a_R[0] = a_O[0]
-- a_L[1] * a_R[1] = a_O[1]
test_arithCircuitProof_shuffle_circuit :: TestTree
test_arithCircuitProof_shuffle_circuit = localOption (QuickCheckTests 20) $
  testProperty "Arithmetic circuit proof. 2 in 2 out shuffle" $ QCM.monadicIO $ do
    let n = 2
        m = 4

    z <- QCM.run Fq.random
    commitBlinders <- QCM.run $ replicateM m Fq.random

    let wL = [[0, 0]
             ,[1, 0]
             ,[0, 1]
             ,[0, 0]
             ,[0, 0]]
        wR = [[0, 0]
             ,[0, 0]
             ,[0, 0]
             ,[1, 0]
             ,[0, 1]]
        wO = [[1, -1]
             ,[0, 0]
             ,[0, 0]
             ,[0, 0]
             ,[0, 0]]
        wV = [[0, 0, 0, 0]
             ,[1, 0, 0, 0]
             ,[0, 0, 1, 0]
             ,[0, 1, 0 ,0]
             ,[0, 0, 0, 1]]
        cs = [0, -z, -z, -z, -z]
        aL = [3 - z, 7 - z]
        aR = [7 - z, 3 - z]
        aO = aL `hadamardp` aR
        vs = [3, 7, 7, 3]
        commitments = zipWith commit vs commitBlinders
        gateWeights = GateWeights wL wR wO
        gateInputs = Assignment aL aR aO
        arithCircuit = ArithCircuit gateWeights wV cs
        arithWitness = ArithWitness gateInputs commitments commitBlinders

    proof <- QCM.run $ generateProof arithCircuit arithWitness

    QCM.assert $ verifyProof commitments proof arithCircuit

