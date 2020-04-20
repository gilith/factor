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
import Factor.Nfs (PolynomialBase(..),PolynomialCoeff(..),PolynomialConfig(..),
                   PolynomialDegree(..),FactorBase,Row)
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

data PositiveOddInteger = PositiveOddInteger Integer
  deriving (Eq,Ord,Show)

instance Arbitrary PositiveOddInteger where
  arbitrary = do
    NonNegative n <- arbitrary
    return $ PositiveOddInteger (2*n + 1)

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

integerLog2Floor :: Positive Integer -> Bool
integerLog2Floor (Positive n) =
    floor (log2Integer n) == widthInteger n - 1

integerJacobiSymbolZero :: Integer -> PositiveOddInteger -> Bool
integerJacobiSymbolZero m (PositiveOddInteger n) =
    (jacobiSymbol m n == ZeroResidue) == not (coprime m n)

integerJacobiSymbolPrime :: Integer -> Positive Int -> Bool
integerJacobiSymbolPrime m (Positive p0) =
    case jacobiSymbol m p of
      ZeroResidue -> True
      Residue -> res
      NonResidue -> not res
  where
    p = Prime.list !! p0  -- Odd prime
    res = any (\i -> Prime.square p i == Prime.fromInteger p m) [1..(p-1)]

integerJacobiSymbolSquare :: Integer -> PositiveOddInteger -> Bool
integerJacobiSymbolSquare m (PositiveOddInteger n) =
    jacobiSymbol (m * m) n == if coprime m n then Residue else ZeroResidue

integerJacobiSymbolMultiplicativeNumerator ::
    Integer -> Integer -> PositiveOddInteger -> Bool
integerJacobiSymbolMultiplicativeNumerator m1 m2 (PositiveOddInteger n) =
    jacobiSymbol (m1 * m2) n ==
    multiplyResidue (jacobiSymbol m1 n) (jacobiSymbol m2 n)

integerJacobiSymbolMultiplicativeDenominator ::
  Integer -> PositiveOddInteger -> PositiveOddInteger -> Bool
integerJacobiSymbolMultiplicativeDenominator
  m (PositiveOddInteger n1) (PositiveOddInteger n2) =
    jacobiSymbol m (n1 * n2) ==
    multiplyResidue (jacobiSymbol m n1) (jacobiSymbol m n2)

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
    test ("Integer width is floor of log2 plus 1",integerLog2Floor)
    test ("Integer Jacobi symbol is zero iff not coprime",integerJacobiSymbolZero)
    test ("Integer Jacobi symbol for primes calculates residues",integerJacobiSymbolPrime)
    test ("Integer Jacobi symbol for squares is residue (or zero)",integerJacobiSymbolSquare)
    test ("Integer Jacobi symbol is multiplicative on numerators",integerJacobiSymbolMultiplicativeNumerator)
    test ("Integer Jacobi symbol is multiplicative on denominators",integerJacobiSymbolMultiplicativeDenominator)

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

data ZxNonZero = ZxNonZero Zx
  deriving (Eq,Ord,Show)

instance Arbitrary ZxNonZero where
  arbitrary = do
    cs <- arbitrary
    NonZero c <- arbitrary
    return $ ZxNonZero (Zx.fromCoeff (cs ++ [c]))

data ZxNonConstant = ZxNonConstant Zx
  deriving (Eq,Ord,Show)

instance Arbitrary ZxNonConstant where
  arbitrary = do
    NonEmpty cs <- arbitrary
    NonZero c <- arbitrary
    return $ ZxNonConstant (Zx.fromCoeff (cs ++ [c]))

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
    NonEmpty cs <- arbitrary
    return $ ZxMonicNotOne (Zx.fromCoeff (cs ++ [1]))

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

zxGcd :: Zx -> Zx -> Bool
zxGcd f g =
    Zx.divides h f &&
    Zx.divides h g &&
    Zx.leadingCoeff h >= 0
  where
    h = Zx.gcd f g

zxSquareFree :: ZxNonConstant -> ZxNonZero -> Bool
zxSquareFree (ZxNonConstant f) (ZxNonZero g) =
    not $ Zx.squareFree (Zx.multiply (Zx.square f) g)

zxSquareFreeDecomposition :: NonEmptyList ZxNonZero -> Bool
zxSquareFreeDecomposition (NonEmpty fs0) =
    (toInteger (sum (zipWith (*) (map Zx.degree fs) [1..])) > maxDegree) ||
    (not (null hs) &&
     all Zx.squareFree hs &&
     Zx.squareFreeRecomposition hs == g)
  where
    fs = map (\(ZxNonZero f) -> f) fs0
    g = Zx.squareFreeRecomposition fs
    hs = Zx.squareFreeDecomposition g

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
    test ("Z[x] gcd divides both arguments",zxGcd)
    test ("Z[x] square-free test has no false positives",zxSquareFree)
    test ("Z[x] square-free decomposition is correct",zxSquareFreeDecomposition)

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

primeSqrt :: PrimeInteger -> Integer -> Bool
primeSqrt (PrimeInteger p) n =
    (Prime.square p (Prime.sqrt p x) /= x) == Prime.nonResidue p n
  where
    x = Prime.fromInteger p n

testPrime :: IO ()
testPrime = do
    test ("Prime integers form a monotonic list starting at 2",primeMonotonic)
    test ("Prime integers are mutually indivisible",primeIndivisible)
    test ("Prime factorization of integers is correct",primeFactor)
    test ("Prime trial division factors all integers",primeTrialDivision)
    test ("Prime exponentiation satisfies Fermat's little theorem",primeFermat)
    test ("Prime inverse is correct",primeInvert)
    test ("Prime square root is correct",primeSqrt)

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
    (Gfpx.isZero h || Gfpx.isMonic h)
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

gfpxFrobeniusValid :: PrimeInteger -> Zx -> Bool
gfpxFrobeniusValid (PrimeInteger p) f0 =
    Gfpx.valid p (Gfpx.frobenius p f)
  where
    f = Gfpx.fromZx p f0

gfpxFrobeniusRange :: PrimeInteger -> Zx -> Bool
gfpxFrobeniusRange (PrimeInteger p) f0 =
    Gfpx.frobeniusRange p (Gfpx.frobenius p f)
  where
    f = Gfpx.fromZx p f0

gfpxFrobeniusRangeDerivative :: PrimeInteger -> Zx -> Bool
gfpxFrobeniusRangeDerivative (PrimeInteger p) f0 =
    Gfpx.frobeniusRange p f == Gfpx.isZero (Gfpx.derivative p f)
  where
    f = Gfpx.fromZx p f0

gfpxFrobeniusInverse :: PrimeInteger -> Zx -> Bool
gfpxFrobeniusInverse (PrimeInteger p) f0 =
    Gfpx.frobeniusInverse p (Gfpx.frobenius p f) == f
  where
    f = Gfpx.fromZx p f0

gfpxSquareFree :: PrimeInteger -> Zx -> Zx -> Bool
gfpxSquareFree (PrimeInteger p) f0 g0 =
    Gfpx.isConstant f ||
    Gfpx.isZero g ||
    not (Gfpx.squareFree p (Gfpx.multiply p (Gfpx.square p f) g))
  where
    f = Gfpx.fromZx p f0
    g = Gfpx.fromZx p g0

gfpxSquareFreeDecomposition :: PrimeInteger -> [Zx] -> Bool
gfpxSquareFreeDecomposition (PrimeInteger p) fs0 =
    (toInteger (sum (zipWith (*) (map Gfpx.degree fs) [1..])) > maxDegree) ||
    null fs ||
    (not (null hs) &&
     all (Gfpx.squareFree p) hs &&
     Gfpx.squareFreeRecomposition p hs == g)
  where
    fs = filter (not . Gfpx.isZero) $ map (Gfpx.fromZx p) fs0
    g = Gfpx.squareFreeRecomposition p fs
    hs = Gfpx.squareFreeDecomposition p g

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
    test ("GF(p)[x] Frobenius endomorphism returns valid data structure",gfpxFrobeniusValid)
    test ("GF(p)[x] Frobenius endomorphism result is in range",gfpxFrobeniusRange)
    test ("GF(p)[x] in Frobenius endomorphism range iff derivative is zero",gfpxFrobeniusRangeDerivative)
    test ("GF(p)[x] Frobenius endomorphism inverse is correct",gfpxFrobeniusInverse)
    test ("GF(p)[x] square-free test has no false positives",gfpxSquareFree)
    test ("GF(p)[x] square-free decomposition is correct",gfpxSquareFreeDecomposition)

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

nfzwNormNegate :: NfzwZx -> Nfzw -> Bool
nfzwNormNegate (NfzwZx f) x =
    Nfzw.norm f (Nfzw.negate x) ==
    (if even (Zx.degree f) then id else negate) (Nfzw.norm f x)

nfzwNormIdeal :: NfzwZx -> Nfzw -> Bool
nfzwNormIdeal (NfzwZx f) x =
    abs n > 1000 ||
    null rps ||
    rps == aps
  where
    n = Nfzw.norm f x
    rps = map fst $ fst $ Prime.trialDivision n
    max_rp = last rps
    aps = map snd $ filter (Nfzw.inIdeal x) $
          takeWhile (\(_,p) -> p <= max_rp) $ Nfzw.ideals f

testNfzw :: IO ()
testNfzw = do
    test ("Z[w] norm is zero iff element is zero",nfzwNormZero)
    test ("Z[w] norm of negation is (-1)^degree(f) * norm",nfzwNormNegate)
    test ("Z[w] norm factorization matches ideal membership",nfzwNormIdeal)

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

instance Arbitrary PolynomialDegree where
  arbitrary = do
    Positive d <- arbitrary
    elements [FixedPolynomialDegree d, OptimalPolynomialDegree]

instance Arbitrary PolynomialBase where
  arbitrary = elements [ClosestPolynomialBase,FloorPolynomialBase]

instance Arbitrary PolynomialCoeff where
  arbitrary = elements [SmallestPolynomialCoeff,PositivePolynomialCoeff]

instance Arbitrary PolynomialConfig where
  arbitrary = do
    degree <- arbitrary
    base <- arbitrary
    coeff <- arbitrary
    return $ PolynomialConfig
               {polynomialDegree = degree,
                polynomialBase = base,
                polynomialCoeff = coeff}

data NfsFactorBase = NfsFactorBase FactorBase
  deriving (Eq,Ord,Show)

instance Arbitrary NfsFactorBase where
  arbitrary = do
    NonNegative n <- arbitrary
    return $ NfsFactorBase (take n Prime.list)

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
    (case Nfs.irreduciblePolynomial h of
       Nothing -> True
       Just _ -> False)
  where
    h = Zx.multiply f g

nfsSelectPolynomialBase :: PolynomialConfig -> NfsInteger -> Bool
nfsSelectPolynomialBase cfg (NfsInteger n) =
    Zx.isMonic f &&
    Zx.degree f >= 1 &&
    Zx.evaluate f m == n
  where
    (f,m) = Nfs.selectPolynomial cfg n

nfsSmoothIntegerNonZero :: NfsFactorBase -> Bool
nfsSmoothIntegerNonZero (NfsFactorBase fb) = not (Nfs.isSmoothInteger fb 0)

nfsGaussianElimination :: NfsMatrix -> Bool
nfsGaussianElimination (NfsMatrix m) =
    length bs >= r - c &&
    all sumRowsZero bs
  where
    r = length m
    c = length (head m)

    bs = Nfs.gaussianElimination m

    sumRowsZero b =
        length b > 0 &&
        all not (foldr addRow (replicate c False) b)
      where
        addRow i s = zipWith (/=) (m !! i) s

testNfs :: IO ()
testNfs = do
    testN 100 ("NFS polynomial irreducibility has no false positives",nfsIrreduciblePolynomial)
    test ("NFS base m polynomial selection is correct",nfsSelectPolynomialBase)
    test ("NFS smooth integer test excludes zero",nfsSmoothIntegerNonZero)
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
