<p align="center">
<a href="https://www.adjoint.io">
  <img width="250" src="./.assets/adjoint.png" alt="Adjoint Logo" />
</a>
</p>

[![CircleCI](http://circleci.com/gh/adjoint-io/bulletproofs.svg?style=shield)](https://circleci.com/gh/adjoint-io/bulletproofs)
[![Hackage](https://img.shields.io/hackage/v/bulletproofs.svg)](http://hackage.haskell.org/package/bulletproofs)

Bulletproofs are short zero-knowledge arguments of knowledge that do not require a trusted setup.
Argument systems are proof systems with computational soundness.

Bulletproofs are suitable for proving statements on committed values, such as range proofs, verifiable suffles, arithmetic circuits, etc.
They rely on the discrete logarithmic assumption and are made non-interactive using
the Fiat-Shamir heuristic.

The core algorithm of Bulletproofs is the inner-product algorithm presented by Groth [2].
The algorithm provides an argument of knowledge of two binding vector Pedersen commitments that satisfy a given inner product relation.
Bulletproofs build on the techniques of Bootle et al. [3] to introduce a communication efficient inner-product proof that reduces
overall communication complexity of the argument to only $2 \log_2(n)$ where $n$ is the dimension
of the two vectors of commitments.


## Range proofs

Bulletproofs present a protocol for conducting short and aggregatable range proofs.
They encode a proof of the range of a committed number in an inner product, using polynomials.
Range proofs are proofs that a secret value lies in a certain interval.
Range proofs do not leak any information about the secret value, other
than the fact that they lie in the interval.

The proof algorithm can be sketched out in 5 steps:

Let $v$ be a value in $[0, n)$ and $\textbf{a}_L$ a vector of bit such that
$\textbf{a}_L \cdot \textbf{2}^n = v$.
The components of $\textbf{a}_L$ are the binary digits of $v$.
We construct a complementary vector $\textbf{a}_R = \textbf{a}_L − \textbf{1}^n$
and require that $\textbf{a}_L \circ \textbf{a}_R = \textbf{0}$ holds.

- $P \rightarrow V : A, S$ - where $A$ and $S$ are blinded Pedersen commitments to $\textbf{a}_L$ and $\textbf{a}_R$.

  $A = h \cdot \alpha + \textbf{g} \cdot \textbf{a}_L + \textbf{h} \cdot \textbf{a}_R \in \mathbb{G}$
  $S = h \cdot \rho + \textbf{g} \cdot \textbf{s}_L + \textbf{h} \cdot \textbf{s}_R \in \mathbb{G}$

- $V \rightarrow P : y, z$ - Verifier sends challenges $y$ and $z$ to fix $A$ and $S$.

- $P \rightarrow V : T_1, T_2$ - where $T_1$ and $T_2$ are commitments to
  the coefficients $t_1$, of a polynomial $t$ constructed from the existing
  values in the protocol.

$\textbf{l} = l(x) = \textbf{a}_L - z \textbf{1}^n + \textbf{s}_L  x \in \mathbb{Z}_p^n$

$\textbf{r} = r(x) = \textbf{y}^n \circ (\textbf{a}_R) + z  \textbf{1}^n + \textbf{s}_R x) + z^2 \textbf{2}^n \in \mathbb{Z}_p^n$

$t = \textbf{l} \cdot \textbf{r} \in \mathbb{Z}_p$

$T_i = g t_i + h \tau_i \in \mathbb{G}$, &nbsp;&nbsp;&nbsp;&nbsp; $i \in \{1, 2\}$

- $V \rightarrow P : x$ - Verifier challenges Prover with value $x$.

- $P \rightarrow V : \tau, \mu, t, \textbf{l}, \textbf{r}$ - Prover sends several commitments that the verifier will then check.

$\tau_x = \tau_2 x^2 + \tau_1 x + z^2 \gamma \in \mathbb{Z}_p$

$\mu = \alpha + \rho x \in \mathbb{Z}_p$

See [Prover.hs](https://github.com/adjoint-io/bulletproofs/blob/master/Bulletproofs/RangeProof/Prover.hs "Prover.hs") for implementation details.

The interaction described is made non-interactive using the Fiat-Shamir Transform wherein all the random
challenges made by V are replaced with a hash of the transcript up until that point.

## Inner-product range proof

The size of the proof is further reduced by leveraging the compact $O(\log_n)$ inner product proof.

The inner-product argument in the protocol allows to prove knowledge of vectors $\textbf{l}$ and $\textbf{r}$, whose inner product is $t$ and
the commitment $P \in  \mathbb{G}$ is a commitment of these two vectors. We can therefore replace sending
($\tau, \mu, t, \textbf{l}, \textbf{r}$) with a transfer of ($\tau, \mu, t$) and an execution of an inner product argument.

Then, instead of sharing $\textbf{l}$ and $\textbf{r}$, which has a communication cost of $2n$ elements, the inner-product
argument transmits only $2 \log_2 + 2$ elements. In total, the prover sends only $2 \log_2(n) + 4$
group elements and 5 elements in $\mathbb{Z}_p$

## Aggregating Logarithmic Proofs

We can construct a single proof of range of multiple values, while only incurring an additional space cost of $2 \log_2(m)$ for
$m$ additional values $v$, as opposed to a multiplicative factor of $m$ when creating $m$ independent range proofs.

The aggregate range proof makes use of the inner product argument. It uses ($2 \log_2 (n  m) + 4$) group elements and 5 elements in $\mathbb{Z}_p$.

See [Multi range proof example](https://github.com/adjoint-io/bulletproofs/tree/master#multi-range-proof)

## Usage

**Single range proof**

```haskell
import Data.Curve.Weierstrass.SECP256K1 (Fr)
import qualified Bulletproofs.RangeProof as RP
import Bulletproofs.Utils (commit)

testSingleRangeProof :: Integer -> (Fr, Fr) -> IO Bool
testSingleRangeProof upperBound (v, vBlinding) = do
  let vCommit = commit v vBlinding

  -- Prover
  proofE <- runExceptT (RP.generateProof upperBound (v, vBlinding))

  -- Verifier
  case proofE of
    Left err -> panic (show err)
    Right proof@RP.RangeProof{..}
      -> pure (RP.verifyProof upperBound vCommit proof)
```

**Multi range proof**

```haskell
import Data.Curve.Weierstrass.SECP256K1 (Fr)
import qualified Bulletproofs.MultiRangeProof as MRP
import Bulletproofs.Utils (commit)

testMultiRangeProof :: Integer -> [(Fr, Fr)] -> IO Bool
testMultiRangeProof upperBound vsAndvBlindings = do
  let vCommits = fmap (uncurry commit) vsAndvBlindings

  -- Prover
  proofE <- runExceptT (MRP.generateProof upperBound vsAndvBlindings)

  -- Verifier
  case proofE of
    Left err -> panic (show err)
    Right proof@RP.RangeProof{..}
      -> pure (MRP.verifyProof upperBound vCommits proof)
```


Note that the upper bound $u$ must be such that $u = 2 ^ n$, where $n$ is also a power of 2.
This implementation uses the elliptic curve secp256k1, a Koblitz curve, which
has 128 bit security.
See [Range proofs examples](./example/Example/RangeProof.hs) for further details.

## Zero-knowledge proofs for Arithmetic Circuits

An arithmetic circuit over a field and variables $(a_1, ..., a_n)$ is a directed acyclic graph whose vertices are called gates.

Arithmetic circuit can be described alternatively as a list of multiplication gates with a collection of linear consistency equations
relating the inputs and outputs of the gates. Any circuit described as an acyclic graph can be efficiently converted into this alternative description.

Bulletproofs present a protocol to generate zero-knowledge argument for arithmetic circuits using the inner product argument,
which allows to get a proof of size $2 \log_2(n) + 13$ elements and include committed values as inputs to the arithmetic circuit.

In the protocol, the Prover proves that the hadamard product of $\textbf{a}_L$ and $\textbf{a}_R$ and a set of linear constraints hold.
The input values $v$ used to generate the proof are then committed and shared with the Verifier.

```haskell
import Data.Curve.Weierstrass.SECP256K1 (Fr)
import Data.Field.Galois (rnd)
import Bulletproofs.ArithmeticCircuit
import Bulletproofs.Utils (hadamard, commit)

--  Example:
--  2 linear constraints (q = 2):
--  aL[0] + aL[1] + aL[2] + aL[3] = v[0]
--  aR[0] + aR[1] + aR[2] + aR[3] = v[1]
--
--  4 multiplication constraints (implicit) (n = 4):
--  aL[0] * aR[0] = aO[0]
--  aL[1] * aR[1] = aO[1]
--  aL[2] * aR[2] = aO[2]
--  aL[3] * aR[3] = aO[3]
--
--  2 input values (m = 2)

arithCircuitExample :: ArithCircuit Fr
arithCircuitExample = ArithCircuit
  { weights = GateWeights
    { wL = [[1, 1, 1, 1]
           ,[0, 0, 0, 0]]
    , wR = [[0, 0, 0, 0]
           ,[1, 1, 1, 1]]
    , wO = [[0, 0, 0, 0]
           ,[0, 0, 0, 0]]
    }
  , commitmentWeights = [[1, 0]
                        ,[0, 1]]
  , cs = [0, 0]
  }

testArithCircuitProof :: ([Fr], [Fr]) -> ArithCircuit Fr -> IO Bool
testArithCircuitProof (aL, aR) arithCircuit = do
  let m = 2

  -- Multiplication constraints
  let aO = aL `hadamard` aR

  -- Linear constraints
      v0 = sum aL
      v1 = sum aR

  commitBlinders <- replicateM m rnd
  let commitments = zipWith commit [v0, v1] commitBlinders

  let arithWitness = ArithWitness
        { assignment = Assignment aL aR aO
        , commitments = commitments
        , commitBlinders = commitBlinders
        }

  proof <- generateProof arithCircuit arithWitness

  pure (verifyProof commitments proof arithCircuit)
```
See [Aritmetic circuit example](./example/Example/ArithmeticCircuit.hs) for further details.

**References**:

1.  Bunz B., Bootle J., Boneh D., Poelstra A., Wuille P., Maxwell G.
    "Bulletproofs: Short Proofs for Confidential Transactions and More". Stanford, UCL, Blockstream, 2017

2. Groth J. "Linear Algebra with Sub-linear Zero-Knowledge Arguments". University College London, 2009

3. Bootle J., Cerully A., Chaidos P., Groth J, Petit C. "Efficient Zero-Knowledge Arguments for
Arithmetic Circuits in the Discrete Log Setting". University College London and University of Oxford, 2016.

**Notation**:

- $\circ$ : Hadamard product
- $\cdot$ :Inner product
- $\textbf{a}$: Vector

## Disclaimer

This is experimental code meant for research-grade projects only. Please do not
use this code in production until it has matured significantly.

## License

```
Copyright 2018-2019 Adjoint Inc

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```
