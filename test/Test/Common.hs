module Test.Common
  ( commutes
  , associates
  , isIdentity
  , isInverse
  , distributes
  ) where

import Protolude

commutes
  :: Eq a
  => (a -> a -> a)
  -> a -> a -> Bool
commutes op x y
  = (x `op` y) == (y `op` x)

associates
  :: Eq a
  => (a -> a -> a)
  -> a -> a -> a -> Bool
associates op x y z
  = (x `op` (y `op` z)) == ((x `op` y) `op` z)

isIdentity
  :: Eq a
  => (a -> a -> a)
  -> a
  -> a
  -> Bool
isIdentity op e x
  = (x `op` e == x) && (e `op` x == x)

isInverse
  :: Eq a
  => (a -> a -> a)
  -> (a -> a)
  -> a
  -> a
  -> Bool
isInverse op inv e x
  = (x `op` inv x == e) && (inv x `op` x == e)

distributes
 :: Eq a
 => (a -> a -> a)
 -> (a -> a -> a)
 -> a
 -> a
 -> a
 -> Bool
distributes mult add x y z
  = x `mult` (y `add` z) == (x `mult` y) `add` (x `mult` z)
