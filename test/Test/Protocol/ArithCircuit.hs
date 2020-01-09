{-# LANGUAGE RecordWildCards, TypeApplications  #-}

module Test.Protocol.ArithCircuit where

import Protolude

import Test.Tasty
import Test.Tasty.QuickCheck
import qualified Test.QuickCheck.Monadic as QCM

import Data.Curve.Weierstrass.SECP256K1 (Fr)

import Bulletproofs.Utils
import Bulletproofs.ArithmeticCircuit
import Bulletproofs.ArithmeticCircuit.Internal

-- | Test an arbitrary circuit
-- Construction:
-- 1. aL, aR, aO; wL, wR, wO; c
--    such that wL * aL + wR * aR + wO * aO = c
--
-- 2. Create wV and v to
--      - reduce the size of the prove (m <= n)
--      - hide assignment
--    wL * aL + wR * aR + wO * aO - c = wV * v
test_arithCircuitProof_arbitrary :: TestTree
test_arithCircuitProof_arbitrary = localOption (QuickCheckTests 10) $
  testProperty "Arbitrary arithmetic circuit proof" $ go
  where
    go :: Property
    go = forAll (arbitrary `suchThat` ((<) 100))
         $ \n -> forAll (arbitrary `suchThat` (\m -> m > 0 && m < n))
         $ \m -> forAll (arithCircuitGen n m)
         $ \arithCircuit@ArithCircuit{..} -> forAll (arithAssignmentGen n)
         $ \assignment@Assignment{..} -> forAll (arithWitnessGen assignment arithCircuit m)
         $ \arithWitness@ArithWitness{..} -> QCM.monadicIO $ do
      proof <- QCM.run $ generateProof arithCircuit arithWitness
      QCM.assert $ verifyProof commitments proof arithCircuit

-- | Test hadamard product relation
--  2 linear constraints (q = 2):
--  aL[0] + aL[1] + ... + aL[15] = v[0]
--  aR[0] + aR[1] + ... + aR[15] = v[1]
--
--  16 multiplication constraints (implicit) (n = 16):
--
--  2 input values (m = 2)
test_arithCircuitProof_hadamard :: TestTree
test_arithCircuitProof_hadamard = localOption (QuickCheckTests 20) $
  testProperty "Arithmetic circuit proof. Hadamard product relation" go
  where
    n = 16
    go :: Fr -> Fr -> Property
    go r s = forAll (vectorOf n (arbitrary @Fr))
        $ \aL -> forAll (vectorOf n arbitrary)
        $ \aR -> QCM.monadicIO $ do
      let aO = aL `hadamard` aR

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

-- | Test that an addition circuit without multiplication gates succeeds
--  1 linear constraints (q = 1):
--  v[0] + v[1] = v[2]
--
--  0 multiplication constraints (implicit) (n = 0):
--
--  3 input values (m = 3)
test_arithCircuitProof_no_mult_gates :: TestTree
test_arithCircuitProof_no_mult_gates = localOption (QuickCheckTests 20) $
  testProperty "Arithmetic circuit proof. n = 0, m = 3, q = 1" go
  where
    m = 3
    go :: Property
    go = forAll (vectorOf (fromIntegral m) (arbitrary @Fr))
         $ \commitBlinders -> QCM.monadicIO $ do
      let wL = [[]]
          wR = [[]]
          wO = [[]]
          cs = [0]
          aL = []
          aR = []
          aO = []
          commitmentWeights = [[1, 1, -1]]
          vs = [2, 5, 7]
          commitments = zipWith commit vs commitBlinders
          gateWeights = GateWeights wL wR wO
          gateInputs = Assignment aL aR aO
          arithCircuit = ArithCircuit gateWeights commitmentWeights cs
          arithWitness = ArithWitness gateInputs commitments commitBlinders

      proof <- QCM.run $ generateProof arithCircuit arithWitness

      QCM.assert $ verifyProof commitments proof arithCircuit

--  | Test that a circuit with a single multiplication gate
--  with linear contraints and not committed values succeeds
--  3 linear constraints (q = 3):
--  aL[0] = 3
--  aR[0] = 4
--  aO[0] = 9
--
--  1 multiplication constraint (implicit) (n = 1):
--  aL[0] * aR[0] = aO[0]
--
--  0 input values (m = 0)
test_arithCircuitProof_no_input_values :: TestTree
test_arithCircuitProof_no_input_values = localOption (QuickCheckTests 20) $
  testProperty "Arithmetic circuit proof. n = 1, m = 0, q = 3" go
  where
    m = 0
    go :: Property
    go = forAll (vectorOf (fromIntegral m) (arbitrary @Fr))
         $ \commitBlinders -> QCM.monadicIO $ do
      let wL = [[0], [0], [1]]
          wR = [[0], [1], [0]]
          wO = [[1], [0], [0]]
          cs = [35, 5, 7]
          aL = [7]
          aR = [5]
          aO = [35]
          commitmentWeights = [[], [], []]
          vs = []
          commitments = zipWith commit vs commitBlinders
          gateWeights = GateWeights wL wR wO
          gateInputs = Assignment aL aR aO
          arithCircuit = ArithCircuit gateWeights commitmentWeights cs
          arithWitness = ArithWitness gateInputs commitments commitBlinders
      proof <- QCM.run $ generateProof arithCircuit arithWitness
      QCM.assert $ verifyProof commitments proof arithCircuit

--  5 linear constraints (q = 5):
--  aO[0] = aO[1]
--  aL[0] = V[0] - z
--  aL[1] = V[2] - z
--  aR[0] = V[1] - z
--  aR[1] = V[3] - z
--
--  2 multiplication constraint (implicit) (n = 2):
--  aL[0] * aR[0] = aO[0]
--  aL[1] * aR[1] = aO[1]
--
--  4 input values (m = 4)
test_arithCircuitProof_shuffle_circuit :: TestTree
test_arithCircuitProof_shuffle_circuit = localOption (QuickCheckTests 20) $
  testProperty "Arithmetic circuit proof. n = 2, m = 4, q = 5" $ go
  where
    go :: Fr -> Property
    go z = forAll (vectorOf 4 (arbitrary @Fr))
        $ \commitBlinders -> QCM.monadicIO $ do

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
          aL = [4 - z, 9 - z]
          aR = [9 - z, 4 - z]
          aO = aL `hadamard` aR
          vs = [4, 9, 9, 4]
          commitments = zipWith commit vs commitBlinders
          gateWeights = GateWeights wL wR wO
          gateInputs = Assignment aL aR aO
          arithCircuit = ArithCircuit gateWeights wV cs
          arithWitness = ArithWitness gateInputs commitments commitBlinders

      proof <- QCM.run $ generateProof arithCircuit arithWitness
      QCM.assert $ verifyProof commitments proof arithCircuit
