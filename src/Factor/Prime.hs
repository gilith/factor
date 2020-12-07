{- |
module: Factor.Prime
description: Prime integers
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}

module Factor.Prime
where

import qualified Data.List as List
import qualified Data.Set as Set
import System.Random (RandomGen)
import qualified System.Random as Random

import Factor.Util

-------------------------------------------------------------------------------
-- The genuine sieve of Eratosthenes
--
-- https://www.cs.hmc.edu/~oneill/papers/Sieve-JFP.pdf
-------------------------------------------------------------------------------

type Prime = Integer

primes :: [Prime]
primes = 2 : 3 : 5 : sieveP 7 ((9,6),Set.empty) (nextQ (drop 2 primes))
  where
    sieveP n ((pk,p),ps) qs =
      case compare n pk of
        LT -> checkQ n ((pk,p),ps) qs
        EQ -> sieveP (n+2) (incrP pk p ps) qs
        GT -> sieveP n (incrP pk p ps) qs

    checkQ n (pk,ps) (q2,q,qs) | n == q2 = sieveP (n+2) pks (nextQ qs)
      where pks = incrP q2 (2*q) (Set.insert pk ps)
    checkQ n ps qs = n : sieveP (n+2) ps qs

    incrP pk p s = Set.deleteFindMin (Set.insert (pk+p, p) s)

    nextQ [] = error "ran out of primes"
    nextQ (q : qs) = (q*q, q, qs)

-------------------------------------------------------------------------------
-- Trial division
-------------------------------------------------------------------------------

type PrimePower = (Prime,Integer)

multiplyPrimePowers :: [PrimePower] -> [PrimePower] -> [PrimePower]
multiplyPrimePowers pks1 [] = pks1
multiplyPrimePowers [] pks2 = pks2
multiplyPrimePowers ((p1,k1) : pks1) ((p2,k2) : pks2) =
    case compare p1 p2 of
      LT -> (p1,k1) : multiplyPrimePowers pks1 ((p2,k2) : pks2)
      EQ -> (p1, k1 + k2) : multiplyPrimePowers pks1 pks2
      GT -> (p2,k2) : multiplyPrimePowers ((p1,k1) : pks1) pks2

productPrimePowers :: [[PrimePower]] -> [PrimePower]
productPrimePowers [] = []
productPrimePowers [pks] = pks
productPrimePowers pksl = multiplyPrimePowers pks1 pks2
  where
    pks1 = productPrimePowers pksl1
    pks2 = productPrimePowers pksl2
    (pksl1,pksl2) = List.splitAt (length pksl `div` 2) pksl

factor :: [Prime] -> Integer -> ([PrimePower],Integer)
factor _ 0 = ([],0)
factor ps n | n < 0 = (pks, Prelude.negate s)
  where (pks,s) = factor ps (Prelude.negate n)
factor ps0 n0 | otherwise = go ps0 n0
  where
    go _ 1 = ([],1)
    go [] n = ([],n)
    go (p : ps) n = (if k == 0 then pks else (p,k) : pks, s)
      where
        (pks,s) = go ps m
        (k,m) = divPower p n

factorProduct :: [Prime] -> [Integer] -> ([PrimePower],[Integer])
factorProduct ps nl = (productPrimePowers pksl, sl)
  where (pksl,sl) = unzip $ map (factor ps) nl

trialDivision :: Integer -> ([PrimePower],Integer)
trialDivision = factor primes

-------------------------------------------------------------------------------
-- Number of primes
--
-- The number of primes at most n is pi(n), which converges to n / log
-- n by the Prime Number Theorem.
--
--   log2(pi(n))
--   ==
--   log2(n / log(n))
--   ==
--   log2(n) - log2(log(n))
--   ==
--   log2(n) - log2(log2(n) / log2(e))
--   ==
--   log2(log2(e)) + log2(n) - log2(log2(n))
--
-- The nth prime function p_n is the inverse to pi and can be
-- estimated by the asymptotic inverse function n * log(n).
--
--   log2(p_n)
--   ==
--   log2(n * log(n))
--   ==
--   log2(n) + log2(log(n))
--   ==
--   log2(n) + log2(log2(n) / log2(e))
--   ==
--   log2(n) + log2(log2(n)) - log2(log2(e))
--
-- https://math.stackexchange.com/questions/606955/estimate-of-nth-prime
-------------------------------------------------------------------------------

primesUnder :: Integer -> Integer
primesUnder n = toInteger (length (takeWhile (\p -> p <= n) primes))

primesUnderEstimate :: Log2Integer -> Log2Integer
primesUnderEstimate = go
  where
    go log2n | log2n <= t = f log2n
    go log2n = max f_t (log2e + log2n - log2 log2n)

    f = log2Integer . primesUnder . exp2Integer

    f_t = f t
    t = 5.0

nthPrime :: Integer -> Integer
nthPrime n = primes !! (Prelude.fromInteger n - 1)

nthPrimeEstimate :: Log2Integer -> Log2Integer
nthPrimeEstimate = go
  where
    go log2n | log2n <= t = f log2n
    go log2n = max f_t (log2n + log2 log2n - log2e)

    f = log2Integer . nthPrime . exp2Integer

    f_t = f t
    t = 5.0

-------------------------------------------------------------------------------
-- B-smooth numbers
--
-- The probability that a uniform integer in the range [1,N] is
-- B-smooth is given there as u^(−u), where u = log N / log B, giving
-- this estimate for the base-2 log of B-smooth integers at most N:
--
--   log2(N * u^(-u))
--   ==
--   log2(N) - u * log2(u)
--
-- For B fixed and much smaller than N, a better estimate is this
-- lower bound (the volume of a B-dimensional shape):
--
--   log2((1 / pi(B)!) * Prod { log2(N) / log2(p) | p <= B })
--   ==
--   Sum { -log2(i) | 1 <= i <= pi(B) }
--   + pi(B) * log2(log2(N))
--   + Sum { -log2(log2(p)) | p <= B }
--
-- Turning this into a probability:
--
--   log2(Prob(random t-bit number is B-smooth))
--   ==
--   log2((2^(smooth_B(t)) - 2^(smooth_B(t-1))) / 2^(t-1))
--   ==
--   (smooth_B(t-1) + log2(2^(smooth_B(t) - smooth_B(t-1)) - 1)) - (t-1)
--
-- For C independent trials:
--
--   log2(Prob(at least one of C random t-bit numbers is B-smooth))
--   ==
--   log2(1 - (1 - 2 ^ (log2(Prob(random t-bit number is B-smooth)))) ^ C)
--   ==
--   log2(1 - (1 - x / C) ^ C)                          [for some x, see below]
--   ==                                    [in the limit as C goes to infinity]
--   log2(1 - e^(-x))
--
-- where
--
--   x / C == 2 ^ (log2(Prob(random t-bit number is B-smooth)))
--   iff
--   x == 2 ^ (log2(Prob(random t-bit number is B-smooth)) + log2(C))
--
-- https://en.wikipedia.org/wiki/Smooth_number#Distribution
-- https://math.stackexchange.com/questions/22949/probability-of-being-b-smooth
-- "Prime Numbers: A Computational Perspective" by Crandall and Pomerance
-------------------------------------------------------------------------------

smoothUnderLowerBound :: Integer -> Log2Integer -> Log2Integer
smoothUnderLowerBound = go (const 0.0) bnds
  where
    go _ [] _ = error "ran out of bounds"
    go f' ((p,f) : pfs) b = if b < p then f' else go f pfs b

    bnds = bndp 0.0 0.0 primes

    bndp _ _ [] = error "ran out of primes"
    bndp i w (p : ps) = (p,f) : bndp i' w' ps
      where
        f log2n = i' * log2 log2n - w'
        i' = i + 1.0
        w' = w + log2 i' + log2 (log2Integer p)

smoothUnder :: Integer -> Log2Integer -> Log2Integer
smoothUnder b log2n =
    if log2n <= log2b then log2n else max lwr (log2n - u * log2 u)
  where
    lwr = (if log2n < fromIntegral b then id
           else max (smoothUnderLowerBound b log2n)) log2b
    u = log2n / log2b
    log2b = log2Integer b

smoothProb :: Integer -> Width -> Log2Probability
smoothProb = prob . smoothUnder
  where
    prob f w = f_t' + log2 (2.0 ** (f t - f_t') - 1.0) - t'
      where
        f_t' = f t'
        t' = t - 1.0
        t = fromIntegral w

smoothProbTrials :: Integer -> Width -> Integer -> Log2Probability
smoothProbTrials b t c = log2 (1.0 - Prelude.exp (-x))
  where x = 2.0 ** (smoothProb b t + log2Integer c)

-------------------------------------------------------------------------------
-- The field GF(p) of arithmetic modulo a prime
-------------------------------------------------------------------------------

type Gfp = Integer

valid :: Prime -> Gfp -> Bool
valid p x = 0 <= x && x < p

fromInt :: Prime -> Int -> Gfp
fromInt p = Factor.Prime.fromInteger p . toInteger

fromInteger :: Prime -> Integer -> Gfp
fromInteger p n = n `mod` p

toSmallestInteger :: Prime -> Gfp -> Integer
toSmallestInteger p x = if p - x < x then x - p else x

negate :: Prime -> Gfp -> Gfp
negate _ 0 = 0
negate p x = p - x

add :: Prime -> Gfp -> Gfp -> Gfp
add p x y = Factor.Prime.fromInteger p (x + y)

sum :: Prime -> [Gfp] -> Gfp
sum p = foldr (add p) 0

subtract :: Prime -> Gfp -> Gfp -> Gfp
subtract p x y = add p x (Factor.Prime.negate p y)

multiply :: Prime -> Gfp -> Gfp -> Gfp
multiply p x y = Factor.Prime.fromInteger p (x * y)

square :: Prime -> Gfp -> Gfp
square p x = multiply p x x

cube :: Prime -> Gfp -> Gfp
cube p x = multiply p x (square p x)

product :: Prime -> [Gfp] -> Gfp
product p = foldr (multiply p) 1

multiplyExp :: Prime -> Gfp -> Gfp -> Integer -> Gfp
multiplyExp _ 0 _ _ = 0
multiplyExp _ z _ 0 = z
multiplyExp _ _ 0 _ = 0
multiplyExp p z0 x0 k0 = go z0 x0 k0
  where
    go z _ 0 = z
    go z 1 _ = z
    go z x k = go z' x' k'
      where
        z' = if even k then z else multiply p z x
        x' = square p x
        k' = k `div` 2

exp :: Prime -> Gfp -> Integer -> Gfp
exp p = multiplyExp p 1

exp2 :: Prime -> Gfp -> Integer -> Gfp
exp2 _ x 0 = x
exp2 p x k = exp2 p (square p x) (k - 1)

invertF :: Prime -> Gfp -> Factor Integer Gfp
invertF _ 0 = error "cannot invert zero"
invertF _ 1 = Right 1
invertF p x = if g == 1 then Right i else Left g
  where
    (g,(_,t)) = egcd p x
    i = if t < 0 then t + p else t

invert :: Prime -> Gfp -> Gfp
invert p x = runFactor $ invertF p x

divideF :: Prime -> Gfp -> Gfp -> Factor Integer Gfp
divideF p x y = do
    z <- invertF p y
    return $ multiply p x z

divide :: Prime -> Gfp -> Gfp -> Gfp
divide p x y = runFactor $ divideF p x y

elements :: Prime -> [Gfp]
elements p = [0 .. (p-1)]

uniform :: RandomGen r => Prime -> r -> (Gfp,r)
uniform p = Random.randomR (0, p - 1)

uniformNonZero :: RandomGen r => Prime -> r -> (Gfp,r)
uniformNonZero p = Random.randomR (1, p - 1)

-------------------------------------------------------------------------------
-- Testing for primality using the Miller-Rabin probabilistic primality test
-------------------------------------------------------------------------------

millerRabinTrials :: Int
millerRabinTrials = 100  -- False positive every 2^200 tests (or so)

isPrime :: RandomGen r => Integer -> r -> (Bool,r)
isPrime n | n <= 3 = (,) (2 <= n)
isPrime n | even n = (,) False
isPrime n = trials millerRabinTrials
  where
    trials 0 r = (True,r)
    trials t r = if trial a then trials (t - 1) r' else (False,r')
      where (a,r') = Random.randomR (2, n - 1) r

    trial a = not $ witness (Factor.Prime.exp n a m) k

    witness x 0 = x /= 1
    witness x i = if x2 == 1 then x /= 1 && x /= n1 else witness x2 (i - 1)
      where x2 = square n x

    (k,m) = divPower 2 n1
    n1 = n - 1

nextPrime :: RandomGen r => Integer -> r -> (Prime,r)
nextPrime n r = if b then (n,r') else nextPrime (n + 1) r'
  where (b,r') = isPrime n r

previousPrime :: RandomGen r => Integer -> r -> (Prime,r)
previousPrime n _ | n < 2 = error "no previous prime"
previousPrime n r = if b then (n,r') else previousPrime (n - 1) r'
  where (b,r') = isPrime n r

uniformPrime :: RandomGen r => Int -> r -> (Prime,r)
uniformPrime w | w < 2 = error $ "no primes with width " ++ show w
uniformPrime 2 = uniformInteger 2
uniformPrime w = pick
  where
    pick r = if b then (n,r'') else pick r''
      where
        (n,r') = uniformOddInteger w r
        (b,r'') = isPrime n r'

uniformComposite :: RandomGen r => Int -> r -> (Integer,r)
uniformComposite w | w < 3 = error $ "no composites with width " ++ show w
uniformComposite w = pick
  where
    pick r = if b then pick r'' else (n,r'')
      where
        (n,r') = uniformInteger w r
        (b,r'') = isPrime n r'

-------------------------------------------------------------------------------
-- Square roots in GF(p) using the Tonelli-Shanks algorithm
-------------------------------------------------------------------------------

isResidue :: Prime -> Integer -> Bool
isResidue p n = jacobiSymbol n p == Residue

nonResidue :: Prime -> Integer -> Bool
nonResidue p n = jacobiSymbol n p == NonResidue

nextResidue :: Prime -> Integer -> Integer
nextResidue p n = if isResidue p n then n else nextResidue p (n + 1)

nextNonResidue :: Prime -> Integer -> Integer
nextNonResidue 2 _ = error "no non-residues modulo 2"
nextNonResidue p n = if nonResidue p n then n else nextNonResidue p (n + 1)

sqrt :: Prime -> Gfp -> Gfp
sqrt 2 = id
sqrt p =
    norm .
    (if r == 1 then sqrt3Mod4
     else if r == 2 then sqrt5Mod8
     else tonelliShanks)
  where
    (r,s) = divPower 2 (p - 1)

    norm x = if 2 * x < p then x else p - x

    sqrt3Mod4 x = Factor.Prime.exp p x sqrt3Mod4Exp

    sqrt3Mod4Exp = (p + 1) `div` 4

    sqrt5Mod8 x = Factor.Prime.product p [x, y, z - 1]
      where
        x2 = multiply p 2 x
        y = Factor.Prime.exp p x2 sqrt5Mod8Exp
        z = multiply p x2 (square p y)

    sqrt5Mod8Exp = (p - 5) `div` 8

    tonelliShanks x =
        if isResidue p x then tonelliShanksLoop tonelliShanksInit d t r else 0
      where
        d = Factor.Prime.exp p x ((s + 1) `div` 2)
        t = Factor.Prime.exp p x s

    tonelliShanksInit = Factor.Prime.exp p (nextNonResidue p 2) s

    tonelliShanksLoop c d t m =
        if t == 1 then d else tonelliShanksLoop b2 db tb2 i
      where
        i = tonelliShanksMin t 1
        b = exp2 p c (m - (i + 1))
        b2 = square p b
        db = multiply p d b
        tb2 = multiply p t b2

    tonelliShanksMin t i = if t2 == 1 then i else tonelliShanksMin t2 (i + 1)
      where t2 = square p t

{-
map (smoothUnder 20 . fromIntegral) [1..100]
map (smoothUnder 40 . fromIntegral) [1..100]
map (smoothUnder 100 . fromIntegral) [1..100]
map (smoothProb 100) [1..100]
map (smoothProb 1000) [1..100]
map (\t -> smoothProbTrials 1000 t 1000) [1..100]
-}
