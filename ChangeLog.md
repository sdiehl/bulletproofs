# Changelog for bulletproofs

## 0.1

* Initial release.
* Implementation of the Bulletproofs protocol for range proofs
* Use of the improved inner-product argument to reduce the communication complexity
* Support for SECp256k1 curve

## 0.2

* Prove and verify computations of arithmetic circuits using Bulletproofs
  protocol.
* Extend range proofs with support for multi-range proofs.
* Add documentation and provide examples to explain and use arithmetic circuits.
* Provide examples for using aggregated range proofs.
* Add multi-range proofs documentation.

## 0.3

* Update dependencies

## 0.4

* Use double exponentiation to improve performance,
* Use Control.Exception.assert to make sure debugging assertions are not checked
  when compiled with optimisations.
* Add benchmarks for rangeproofs.
