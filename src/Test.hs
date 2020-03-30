{- |
module: Main
description: Testing the library for factoring positive integers
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Main
  ( main )
where

import Test.QuickCheck

import Factor.Gaussian (Gaussian(..))
import qualified Factor.Gaussian as Gaussian
import qualified Factor.Gfpx as Gfpx
import Factor.Nfs (Row)
import qualified Factor.Nfs as Nfs
import Factor.Nfzw (Nfzw(..))
import qualified Factor.Nfzw as Nfzw
import qualified Factor.Prime as Prime
import Factor.Util
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDegree :: Integer
maxDegree = 100

--------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------

checkWith :: Testable prop => Args -> (String,prop) -> IO ()
checkWith args (desc,prop) = do
    putStr (desc ++ " ")
    res <- quickCheckWithResult args prop
    case res of
      Failure {} -> error "Proposition failed"
      _ -> return ()

testN :: Testable prop => Int -> (String,prop) -> IO ()
testN n = checkWith $ stdArgs {maxSuccess = n}

test :: Testable prop => (String,prop) -> IO ()
test = testN 1000

{- No assertions yet
assert :: (String,Bool) -> IO ()
assert = checkWith $ stdArgs {maxSuccess = 1}
-}

-------------------------------------------------------------------------------
-- Testing the utility functions
-------------------------------------------------------------------------------

integerDivision :: Integer -> (NonZero Integer) -> Bool
integerDivision m (NonZero n) =
    m == q*n + r &&
    0 <= r &&
    r < abs n
  where
    (q,r) = division m n

integerDivisionDivMod :: Integer -> Positive Integer -> Bool
integerDivisionDivMod m (Positive n) =
    q == m `div` n &&
    r == m `mod` n
  where
    (q,r) = division m n

integerDivisionClosest :: Integer -> (NonZero Integer) -> Bool
integerDivisionClosest m (NonZero n) =
    m == q*n + r &&
    -((abs n - 1) `div` 2) <= r &&
    r <= (abs n `div` 2)
  where
    (q,r) = divisionClosest m n

integerDivPower :: Positive Integer -> Integer -> Bool
integerDivPower (Positive m0) n =
    n == m^k * s &&
    (if n == 0 then k == 0 else not (divides (m^(k+1)) n))
  where
    (k,s) = divPower m n
    m = m0 + 1

integerEgcd :: Integer -> Integer -> Bool
integerEgcd m n =
    divides g m &&
    divides g n &&
    s*m + t*n == g &&
    0 <= g
  where
    (g,(s,t)) = egcd m n

integerEgcdGcd :: Integer -> Integer -> Bool
integerEgcdGcd m n = fst (egcd m n) == gcd m n

integerNthRoot :: Positive Int -> NonNegative Integer -> Bool
integerNthRoot (Positive n) (NonNegative k) =
    p^n <= k &&
    k < (p+1)^n
  where
    p = nthRoot n k

integerNthRootClosest :: Positive Int -> NonNegative Integer -> Bool
integerNthRootClosest (Positive n) (NonNegative k) =
    case compare (p^n) k of
      LT -> k - p^n <= abs (k - (p+1)^n)
      EQ -> True
      GT -> p^n - k < abs (k - (p-1)^n)
  where
    p = nthRootClosest n k

testUtil :: IO ()
testUtil = do
    test ("Integer division is correct",integerDivision)
    test ("Integer division agrees with built-in div and mod",integerDivisionDivMod)
    test ("Integer closest division is correct",integerDivisionClosest)
    test ("Integer division by power is correct",integerDivPower)
    test ("Integer extended gcd is correct",integerEgcd)
    test ("Integer extended gcd agrees with built-in gcd",integerEgcdGcd)
    test ("Integer nth root is correct",integerNthRoot)
    test ("Integer closest nth root is correct",integerNthRootClosest)

-------------------------------------------------------------------------------
-- Testing Gaussian integers
-------------------------------------------------------------------------------

instance Arbitrary Gaussian where
  arbitrary = do
    a <- arbitrary
    b <- arbitrary
    return (Gaussian a b)

gaussianNormNonNegative :: Gaussian -> Bool
gaussianNormNonNegative x =
    n >= 0 &&
    ((n == 0) == (x == Gaussian.zero))
  where
    n = Gaussian.norm x

gaussianNormMonotonic :: Gaussian -> Gaussian -> Bool
gaussianNormMonotonic x y =
    y == Gaussian.zero ||
    Gaussian.norm x <= Gaussian.norm (Gaussian.multiply x y)

gaussianDivision :: Gaussian -> Gaussian -> Bool
gaussianDivision x y =
    y == Gaussian.zero ||
    ((x == Gaussian.add (Gaussian.multiply q y) r) &&
     (Gaussian.norm r <= Gaussian.norm y `div` 2))
  where
    (q,r) = Gaussian.division x y

gaussianEgcd :: Gaussian -> Gaussian -> Bool
gaussianEgcd x y =
    Gaussian.divides g x &&
    Gaussian.divides g y &&
    Gaussian.add (Gaussian.multiply s x) (Gaussian.multiply t y) == g
  where
    (g,(s,t)) = Gaussian.egcd x y

testGaussian :: IO ()
testGaussian = do
    test ("Gaussian integer norm is non-negative",gaussianNormNonNegative)
    test ("Gaussian integer norm is monotonic",gaussianNormMonotonic)
    test ("Gaussian integer division is correct",gaussianDivision)
    test ("Gaussian integer extended gcd is correct",gaussianEgcd)

-------------------------------------------------------------------------------
-- Testing the polynomial ring Z[x]
-------------------------------------------------------------------------------

instance Arbitrary Zx where
  arbitrary = fmap Zx.fromCoeff arbitrary

data ZxMonic = ZxMonic Zx
  deriving (Eq,Ord,Show)

instance Arbitrary ZxMonic where
  arbitrary = do
    cs <- arbitrary
    return $ ZxMonic (Zx.fromCoeff (cs ++ [1]))

data ZxMonicNotOne = ZxMonicNotOne Zx
  deriving (Eq,Ord,Show)

instance Arbitrary ZxMonicNotOne where
  arbitrary = do
    c <- arbitrary
    cs <- arbitrary
    return $ ZxMonicNotOne (Zx.fromCoeff (c : cs ++ [1]))

data ZxPrimitive = ZxPrimitive Zx
  deriving (Eq,Ord,Show)

instance Arbitrary ZxPrimitive where
  arbitrary = fmap (ZxPrimitive . Zx.primitive) arbitrary

zxFromCoeffValid :: [Integer] -> Bool
zxFromCoeffValid = Zx.valid . Zx.fromCoeff

zxConstantEvaluate :: Integer -> Integer -> Bool
zxConstantEvaluate c x = Zx.evaluate (Zx.constant c) x == c

zxDerivativeValid :: Zx -> Bool
zxDerivativeValid = Zx.valid . Zx.derivative

zxNegateValid :: Zx -> Bool
zxNegateValid = Zx.valid . Zx.negate

zxNegateDegree :: Zx -> Bool
zxNegateDegree f = Zx.degree (Zx.negate f) == Zx.degree f

zxNegateEvaluate :: Zx -> Integer -> Bool
zxNegateEvaluate f x = Zx.evaluate (Zx.negate f) x == negate (Zx.evaluate f x)

zxAddValid :: Zx -> Zx -> Bool
zxAddValid f g = Zx.valid (Zx.add f g)

zxAddDegree :: Zx -> Zx -> Bool
zxAddDegree f g = Zx.degree (Zx.add f g) <= max (Zx.degree f) (Zx.degree g)

zxAddEvaluate :: Zx -> Zx -> Integer -> Bool
zxAddEvaluate f g x =
    Zx.evaluate (Zx.add f g) x == Zx.evaluate f x + Zx.evaluate g x

zxMultiplyValid :: Zx -> Zx -> Bool
zxMultiplyValid f g = Zx.valid (Zx.multiply f g)

zxMultiplyDegree :: Zx -> Zx -> Bool
zxMultiplyDegree f g =
    if fd < 0 || gd < 0 then d < 0 else d == fd + gd
  where
    d = Zx.degree (Zx.multiply f g)
    fd = Zx.degree f
    gd = Zx.degree g

zxMultiplyEvaluate :: Zx -> Zx -> Integer -> Bool
zxMultiplyEvaluate f g x =
    Zx.evaluate (Zx.multiply f g) x == Zx.evaluate f x * Zx.evaluate g x

zxMultiplyConstantValid :: Integer -> Zx -> Bool
zxMultiplyConstantValid n f = Zx.valid (Zx.multiplyConstant n f)

zxMultiplyPowerValid :: NonNegative Int -> Zx -> Bool
zxMultiplyPowerValid (NonNegative d) f = Zx.valid (Zx.multiplyPower d f)

zxDivision :: Zx -> Zx -> Bool
zxDivision f g =
    Zx.isZero g ||
    ((f == Zx.add (Zx.multiply q g) r) &&
     (Zx.degree r <= Zx.degree f))
  where
    (q,r) = Zx.division f g

zxDivisionMonic :: Zx -> ZxMonic -> Bool
zxDivisionMonic f (ZxMonic m) =
    (f == Zx.add (Zx.multiply q m) r) &&
    (Zx.degree r < Zx.degree m)
  where
    (q,r) = Zx.division f m

zxQuotientMultiply :: Zx -> Zx -> Bool
zxQuotientMultiply f g =
    Zx.isZero f ||
    (Zx.quotient (Zx.multiply f g) f == g)

zxContentPrimitive :: Zx -> Bool
zxContentPrimitive f =
    0 <= c &&
    Zx.isPrimitive p &&
    f == Zx.multiplyConstant c p
  where
    c = Zx.content f
    p = Zx.primitive f

zxGaussLemma :: ZxPrimitive -> ZxPrimitive -> Bool
zxGaussLemma (ZxPrimitive f) (ZxPrimitive g) =
    Zx.isPrimitive (Zx.multiply f g)

testZx :: IO ()
testZx = do
    test ("Z[x] constructor returns valid data structure",zxFromCoeffValid)
    test ("Z[x] constant polynomial evaluation",zxConstantEvaluate)
    test ("Z[x] derivative returns valid data structure",zxDerivativeValid)
    test ("Z[x] negation returns valid data structure",zxNegateValid)
    test ("Z[x] negation preserves degree",zxNegateDegree)
    test ("Z[x] negation evaluation",zxNegateEvaluate)
    test ("Z[x] addition returns valid data structure",zxAddValid)
    test ("Z[x] addition degree in correct range",zxAddDegree)
    test ("Z[x] addition evaluation",zxAddEvaluate)
    test ("Z[x] multiplication returns valid data structure",zxMultiplyValid)
    test ("Z[x] multiplication degree is correct",zxMultiplyDegree)
    test ("Z[x] multiplication evaluation",zxMultiplyEvaluate)
    test ("Z[x] multiplication by a constant returns valid data structure",zxMultiplyConstantValid)
    test ("Z[x] multiplication by a power returns valid data structure",zxMultiplyPowerValid)
    test ("Z[x] division satisfies f == q*g + r",zxDivision)
    test ("Z[x] division by a monic polynomial",zxDivisionMonic)
    test ("Z[x] quotient satisfies (f*g) / f == g",zxQuotientMultiply)
    test ("Z[x] decomposition into content and primitive part",zxContentPrimitive)
    test ("Z[x] product of primitive polynomials is primitive",zxGaussLemma)

-------------------------------------------------------------------------------
-- Testing primes
-------------------------------------------------------------------------------

data PrimeInteger = PrimeInteger Integer
  deriving (Eq,Ord,Show)

instance Arbitrary PrimeInteger where
  arbitrary = do
    NonNegative i <- arbitrary
    return $ PrimeInteger (Prime.list !! i)

primeMonotonic :: NonNegative Int -> Bool
primeMonotonic (NonNegative i) =
    if i == 0 then p == 2 else (Prime.list !! (i-1)) < p
  where
    p = Prime.list !! i

primeIndivisible :: NonNegative Int -> Bool
primeIndivisible (NonNegative i) =
    all (\q -> not (divides q p)) (take i Prime.list)
  where
    p = Prime.list !! i

primeFactor :: [NonNegative Int] -> Integer -> Bool
primeFactor il n =
    m == n
  where
    m = foldr (\(p,k) z -> p^k * z) s pks
    (pks,s) = Prime.factor ps n
    (ps,_) = foldr nextP ([],Prime.list) il
    nextP (NonNegative i) (x,y) = let z = drop i y in (head z : x, tail z)

primeTrialDivision :: Integer -> Bool
primeTrialDivision n =
    m == n &&
    (case compare n 0 of
       LT -> s == -1
       EQ -> null pks && s == 0
       GT -> s == 1)
  where
    m = foldr (\(p,k) z -> p^k * z) s pks
    (pks,s) = Prime.trialDivision n

primeFermat :: PrimeInteger -> Integer -> Bool
primeFermat (PrimeInteger p) n =
    Prime.exp p x p == x
  where
    x = Prime.fromInteger p n

primeInvert :: PrimeInteger -> Integer -> Bool
primeInvert (PrimeInteger p) n =
    x == 0 ||
    (Prime.valid p y &&
     Prime.multiply p x y == 1)
  where
    x = Prime.fromInteger p n
    y = Prime.invert p x

testPrime :: IO ()
testPrime = do
    test ("Prime integers form a monotonic list starting at 2",primeMonotonic)
    test ("Prime integers are mutually indivisible",primeIndivisible)
    test ("Prime factorization of integers is correct",primeFactor)
    test ("Prime trial division factors all integers",primeTrialDivision)
    test ("Prime exponentiation satisfies Fermat's little theorem",primeFermat)
    test ("Prime inverse is correct",primeInvert)

-------------------------------------------------------------------------------
-- Testing the polynomial ring GF(p)[x]
-------------------------------------------------------------------------------

gfpxFromZxValid :: PrimeInteger -> Zx -> Bool
gfpxFromZxValid (PrimeInteger p) = Gfpx.valid p . Gfpx.fromZx p

gfpxConstantEvaluate :: PrimeInteger -> Integer -> Integer -> Bool
gfpxConstantEvaluate (PrimeInteger p) c0 x0 =
    Gfpx.evaluate p (Gfpx.constant c) x == c
  where
    c = Prime.fromInteger p c0
    x = Prime.fromInteger p x0

gfpxDerivativeValid :: PrimeInteger -> Zx -> Bool
gfpxDerivativeValid (PrimeInteger p) f0 =
    Gfpx.valid p (Gfpx.derivative p f)
  where
    f = Gfpx.fromZx p f0

gfpxNegateValid :: PrimeInteger -> Zx -> Bool
gfpxNegateValid (PrimeInteger p) f0 =
    Gfpx.valid p (Gfpx.negate p f)
  where
    f = Gfpx.fromZx p f0

gfpxNegateDegree :: PrimeInteger -> Zx -> Bool
gfpxNegateDegree (PrimeInteger p) f0 =
    Gfpx.degree (Gfpx.negate p f) == Gfpx.degree f
  where
    f = Gfpx.fromZx p f0

gfpxNegateEvaluate :: PrimeInteger -> Zx -> Integer -> Bool
gfpxNegateEvaluate (PrimeInteger p) f0 x0 =
    Gfpx.evaluate p (Gfpx.negate p f) x == Prime.negate p (Gfpx.evaluate p f x)
  where
    f = Gfpx.fromZx p f0
    x = Prime.fromInteger p x0

gfpxAddValid :: PrimeInteger -> Zx -> Zx -> Bool
gfpxAddValid (PrimeInteger p) f0 g0 =
    Gfpx.valid p (Gfpx.add p f g)
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0

gfpxAddDegree :: PrimeInteger -> Zx -> Zx -> Bool
gfpxAddDegree (PrimeInteger p) f0 g0 =
    Gfpx.degree (Gfpx.add p f g) <= max (Gfpx.degree f) (Gfpx.degree g)
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0

gfpxAddEvaluate :: PrimeInteger -> Zx -> Zx -> Integer -> Bool
gfpxAddEvaluate (PrimeInteger p) f0 g0 x0 =
    Gfpx.evaluate p (Gfpx.add p f g) x ==
    Prime.add p (Gfpx.evaluate p f x) (Gfpx.evaluate p g x)
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0
    x = Prime.fromInteger p x0

gfpxMultiplyValid :: PrimeInteger -> Zx -> Zx -> Bool
gfpxMultiplyValid (PrimeInteger p) f0 g0 =
    Gfpx.valid p (Gfpx.multiply p f g)
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0

gfpxMultiplyDegree :: PrimeInteger -> Zx -> Zx -> Bool
gfpxMultiplyDegree (PrimeInteger p) f0 g0 =
    if fd < 0 || gd < 0 then d < 0 else d == fd + gd
  where
    d = Gfpx.degree (Gfpx.multiply p f g)
    fd = Gfpx.degree f
    gd = Gfpx.degree g
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0

gfpxMultiplyEvaluate :: PrimeInteger -> Zx -> Zx -> Integer -> Bool
gfpxMultiplyEvaluate (PrimeInteger p) f0 g0 x0 =
    Gfpx.evaluate p (Gfpx.multiply p f g) x ==
    Prime.multiply p (Gfpx.evaluate p f x) (Gfpx.evaluate p g x)
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0
    x = Prime.fromInteger p x0

gfpxMultiplyConstantValid :: PrimeInteger -> Integer -> Zx -> Bool
gfpxMultiplyConstantValid (PrimeInteger p) x0 f0 =
    Gfpx.valid p (Gfpx.multiplyConstant p x f)
  where
    x = Prime.fromInteger p x0
    f = Gfpx.fromZx p f0

gfpxMultiplyPowerValid :: PrimeInteger -> NonNegative Int -> Zx -> Bool
gfpxMultiplyPowerValid (PrimeInteger p) (NonNegative d) f0 =
    Gfpx.valid p (Gfpx.multiplyPower d f)
  where
    f = Gfpx.fromZx p f0

gfpxDivision :: PrimeInteger -> Zx -> Zx -> Bool
gfpxDivision (PrimeInteger p) f0 g0 =
    Gfpx.isZero g ||
    ((f == Gfpx.add p (Gfpx.multiply p q g) r) &&
     (Gfpx.degree r < Gfpx.degree g))
  where
    (q,r) = Gfpx.division p f g
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0

gfpxQuotientMultiply :: PrimeInteger -> Zx -> Zx -> Bool
gfpxQuotientMultiply (PrimeInteger p) f0 g0 =
    Gfpx.isZero f ||
    (Gfpx.quotient p (Gfpx.multiply p f g) f == g)
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0

gfpxEgcd :: PrimeInteger -> Zx -> Zx -> Bool
gfpxEgcd (PrimeInteger p) f0 g0 =
    Gfpx.divides p h f &&
    Gfpx.divides p h g &&
    Gfpx.add p (Gfpx.multiply p s f) (Gfpx.multiply p t g) == h &&
    (Gfpx.isZero h || Gfpx.powerCoeff h (Gfpx.degree h) == 1)
  where
    (h,(s,t)) = Gfpx.egcd p f g
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0

gfpxComposeEvaluate :: PrimeInteger -> Zx -> Zx -> Integer -> Bool
gfpxComposeEvaluate (PrimeInteger p) f0 g0 x0 =
    (toInteger (Gfpx.degree f * Gfpx.degree g) > maxDegree) ||
    (Gfpx.evaluate p (Gfpx.compose p f g) x ==
     Gfpx.evaluate p f (Gfpx.evaluate p g x))
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0
    x = Prime.fromInteger p x0

gfpxMultiplyExpRemainder :: PrimeInteger -> Zx -> Zx -> Zx -> (NonNegative Integer) -> Bool
gfpxMultiplyExpRemainder (PrimeInteger p) f0 g0 h0 (NonNegative k) =
    (toInteger (Gfpx.degree f) + toInteger (Gfpx.degree g) * k > maxDegree) ||
    (Gfpx.isZero f) ||
    (Gfpx.multiplyExpRemainder p f g h k ==
     Gfpx.remainder p (Gfpx.multiplyExp p g h k) f)
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0
    h = Gfpx.fromZx p h0

gfpxRoots :: PrimeInteger -> Zx -> Bool
gfpxRoots (PrimeInteger p) f0 =
    Gfpx.roots p f == filter (\x -> Gfpx.evaluate p f x == 0) [0..(p-1)]
  where
    f = Gfpx.fromZx p f0

gfpxIrreducible :: PrimeInteger -> ZxMonicNotOne -> ZxMonicNotOne -> Bool
gfpxIrreducible (PrimeInteger p) (ZxMonicNotOne f0) (ZxMonicNotOne g0) =
    toInteger (Gfpx.degree h) > maxDegree `div` 2 ||
    not (Gfpx.irreducible p h)
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0
    h = Gfpx.multiply p f g

testGfpx :: IO ()
testGfpx = do
    test ("GF(p)[x] constructor returns valid data structure",gfpxFromZxValid)
    test ("GF(p)[x] constant polynomial evaluation",gfpxConstantEvaluate)
    test ("GF(p)[x] derivative returns valid data structure",gfpxDerivativeValid)
    test ("GF(p)[x] negation returns valid data structure",gfpxNegateValid)
    test ("GF(p)[x] negation preserves degree",gfpxNegateDegree)
    test ("GF(p)[x] negation evaluation",gfpxNegateEvaluate)
    test ("GF(p)[x] addition returns valid data structure",gfpxAddValid)
    test ("GF(p)[x] addition degree in correct range",gfpxAddDegree)
    test ("GF(p)[x] addition evaluation",gfpxAddEvaluate)
    test ("GF(p)[x] multiplication returns valid data structure",gfpxMultiplyValid)
    test ("GF(p)[x] multiplication degree is correct",gfpxMultiplyDegree)
    test ("GF(p)[x] multiplication evaluation",gfpxMultiplyEvaluate)
    test ("GF(p)[x] multiplication by a constant returns valid data structure",gfpxMultiplyConstantValid)
    test ("GF(p)[x] multiplication by a power returns valid data structure",gfpxMultiplyPowerValid)
    test ("GF(p)[x] division satisfies f == q*g + r",gfpxDivision)
    test ("GF(p)[x] quotient satisfies (f*g) / f == g",gfpxQuotientMultiply)
    test ("GF(p)[x] extended gcd is correct",gfpxEgcd)
    test ("GF(p)[x] composition evaluation",gfpxComposeEvaluate)
    test ("GF(p)[x] modular exponentiation is correct",gfpxMultiplyExpRemainder)
    test ("GF(p)[x] root finding is correct",gfpxRoots)
    test ("GF(p)[x] irreducibility test is correct",gfpxIrreducible)

-------------------------------------------------------------------------------
-- Testing the subring Z[w] of the number field Q(w)
-------------------------------------------------------------------------------

instance Arbitrary Nfzw where
  arbitrary = do
    a <- arbitrary
    b <- arbitrary
    let g = gcd a b
    return $ if g == 0 then Nfzw a b else Nfzw (a `div` g) (b `div` g)

data NfzwZx = NfzwZx Zx
  deriving (Eq,Ord,Show)

instance Arbitrary NfzwZx where
  arbitrary = do
    NonZero c <- arbitrary
    cs <- arbitrary
    return $ NfzwZx (Zx.fromCoeff (c : cs ++ [1]))

nfzwNormZero :: NfzwZx -> Nfzw -> Bool
nfzwNormZero (NfzwZx f) x =
    (Nfzw.norm f x == 0) == isZero x
  where
    isZero (Nfzw 0 0) = True
    isZero (Nfzw a 1) = Zx.evaluate f (negate a) == 0
    isZero (Nfzw a (-1)) = Zx.evaluate f a == 0
    isZero _ = False

nfzwNormFactor :: NfzwZx -> Nfzw -> Bool
nfzwNormFactor (NfzwZx f) x =
    null rps ||
    rps == aps
  where
    rps = map fst $ fst $ Prime.trialDivision $ Nfzw.norm f x
    max_rp = last rps
    aps = map snd $ filter (Nfzw.inIdeal x) $
          takeWhile (\(_,p) -> p <= max_rp) $ Nfzw.ideals f

testNfzw :: IO ()
testNfzw = do
    test ("Z[w] norm is zero iff element is zero",nfzwNormZero)
    testN 1 ("Z[w] norm factorization matches ideal membership",nfzwNormFactor)

-------------------------------------------------------------------------------
-- Testing the number field sieve
-------------------------------------------------------------------------------

data NfsInteger = NfsInteger Integer
  deriving (Eq,Ord,Show)

instance Arbitrary NfsInteger where
  arbitrary = do
    Positive m0 <- arbitrary
    NonNegative n0 <- arbitrary
    let m = 2*m0 + 5
    let n = m + 2*n0
    return $ NfsInteger (m * n)

data NfsMatrix = NfsMatrix [Row]
  deriving (Eq,Ord,Show)

instance Arbitrary NfsMatrix where
  arbitrary = do
    Positive c <- arbitrary
    NonNegative r0 <- arbitrary
    let r = c + r0
    m <- vectorOf r (vector c)
    return $ NfsMatrix m

nfsIrreduciblePolynomial :: ZxMonicNotOne -> ZxMonicNotOne -> Bool
nfsIrreduciblePolynomial (ZxMonicNotOne f) (ZxMonicNotOne g) =
    toInteger (Zx.degree h) > maxDegree `div` 5 ||
    not (Nfs.irreduciblePolynomial h)
  where
    h = Zx.multiply f g

nfsSelectPolynomialBase :: Bool -> NfsInteger -> Positive Int -> Bool
nfsSelectPolynomialBase pos (NfsInteger n) (Positive d) =
    Zx.isMonic f &&
    Zx.degree f == d &&
    Zx.evaluate f m == n
  where
    (f,m) = Nfs.selectPolynomialBase pos n d

nfsGaussianElimination :: NfsMatrix -> Bool
nfsGaussianElimination (NfsMatrix m) =
    length bs >= r - c &&
    all sumRowsTrue bs
  where
    r = length m
    c = length (head m)

    bs = Nfs.gaussianElimination m

    sumRowsTrue b =
        length b > 0 &&
        all id (foldr addRow (replicate c True) b)
      where
        addRow i s = zipWith (==) (m !! i) s

testNfs :: IO ()
testNfs = do
    testN 100 ("NFS polynomial irreducibility has no false positives",nfsIrreduciblePolynomial)
    test ("NFS base m polynomial selection is correct",nfsSelectPolynomialBase)
    test ("NFS Gaussian elimination is correct",nfsGaussianElimination)

--------------------------------------------------------------------------------
-- Main function
--------------------------------------------------------------------------------

main :: IO ()
main = do
    testUtil
    testGaussian
    testZx
    testPrime
    testGfpx
    testNfzw
    testNfs
