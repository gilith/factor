{- |
module: Factor.Gfpx
description: The polynomial ring GF(p)[x]
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Gfpx
where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as List
import System.Random (RandomGen)

import Factor.Prime (Gfp,Prime)
import qualified Factor.Prime as Prime
import qualified Factor.Util as Util
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- The polynomial ring GF(p)[x]
-------------------------------------------------------------------------------

data Gfpx =
    Gfpx
      {degree :: Int,
       coeffMap :: IntMap Gfp}
  deriving (Eq,Ord)

instance Show Gfpx where
  show = show . toZx

valid :: Prime -> Gfpx -> Bool
valid p f =
    Zx.valid (toZx f) &&
    all (Prime.valid p) (IntMap.elems (coeffMap f))

fromNormCoeffMap :: IntMap Gfp -> Gfpx
fromNormCoeffMap c | IntMap.null c = zero
fromNormCoeffMap c | otherwise = Gfpx {degree = d, coeffMap = c}
  where (d,_) = IntMap.findMax c

fromCoeffMap :: IntMap Gfp -> Gfpx
fromCoeffMap = fromNormCoeffMap . IntMap.filter ((/=) 0)

-------------------------------------------------------------------------------
-- Polynomial operations
-------------------------------------------------------------------------------

isZero :: Gfpx -> Bool
isZero f = degree f < 0

isOne :: Gfpx -> Bool
isOne f = f == one

isConstant :: Gfpx -> Bool
isConstant f = degree f <= 0

isLinear :: Gfpx -> Bool
isLinear f = degree f <= 1

isMonic :: Gfpx -> Bool
isMonic f = leadingCoeff f == 1

constMonic :: Prime -> Gfpx -> (Gfp,Gfpx)
constMonic p f =
    case leadingCoeff f of
      0 -> error "constMonic: zero polynomial"
      1 -> (1,f)
      c -> (c, multiplyConstant p (Prime.invert p c) f)

powerCoeff :: Gfpx -> Int -> Gfp
powerCoeff f i = IntMap.findWithDefault 0 i (coeffMap f)

constantCoeff :: Gfpx -> Gfp
constantCoeff f = powerCoeff f 0

linearCoeff :: Gfpx -> Gfp
linearCoeff f = powerCoeff f 1

leadingCoeff :: Gfpx -> Gfp
leadingCoeff f = powerCoeff f (degree f)

monomials :: Gfpx -> [(Int,Gfp)]
monomials = IntMap.toAscList . coeffMap

lengthMonomials :: Gfpx -> Int
lengthMonomials = IntMap.size . coeffMap

filterMonomials :: (Int -> Gfp -> Bool) -> Gfpx -> Gfpx
filterMonomials p = fromNormCoeffMap . IntMap.filterWithKey p . coeffMap

constant :: Gfp -> Gfpx
constant = monomial 0

variable :: Gfpx
variable = monomial 1 1

monomial :: Int -> Gfp -> Gfpx
monomial _ 0 = zero
monomial d x = Gfpx {degree = d, coeffMap = IntMap.singleton d x}

simpleRoot :: Prime -> Gfp -> Gfpx
simpleRoot p r = Factor.Gfpx.subtract p variable (constant r)

evaluate :: Prime -> Gfpx -> Gfp -> Gfp
evaluate p f x = align 0 $ IntMap.foldrWithKey fma (0,0) $ coeffMap f
  where
    fma i c z = (i, Prime.add p (align i z) c)

    align i (d,z) =
        if k <= 0 then z else Prime.multiplyExp p z x (toInteger k)
      where
        k = d - i

derivative :: Prime -> Gfpx -> Gfpx
derivative p (Gfpx {degree = d, coeffMap = cm}) =
    if d <= 0 then zero
    else multiplyPower (-1) $ fromNormCoeffMap $ deriv cm
  where
    deriv = IntMap.mapMaybeWithKey multDeg
    multDeg i c = if c' == 0 then Nothing else Just c'
      where c' = Prime.multiply p (Prime.fromInt p i) c

fromCoeff :: [Gfp] -> Gfpx
fromCoeff = fromCoeffMap . IntMap.fromList . zip [0..]

fromZx :: Prime -> Zx -> Gfpx
fromZx p = fromNormCoeffMap . IntMap.mapMaybe f . Zx.coeffMap
  where
    f c = if x == 0 then Nothing else Just x
      where x = Prime.fromInteger p c

toZx :: Gfpx -> Zx
toZx (Gfpx {degree = d, coeffMap = c}) = Zx.Zx {Zx.degree = d, Zx.coeffMap = c}

toSmallestZx :: Prime -> Gfpx -> Zx
toSmallestZx p (Gfpx {degree = d, coeffMap = c}) =
    Zx.Zx {Zx.degree = d, Zx.coeffMap = IntMap.map (Prime.toSmallestInteger p) c}

uniform :: RandomGen r => Prime -> Int -> r -> (Gfpx,r)
uniform _ d r | d < 0 = (zero,r)
uniform p d r = (fromCoeff l, r')
  where (l,r') = Util.unfoldrN (Prime.uniform p) (d + 1) r

-------------------------------------------------------------------------------
-- Ring operations
-------------------------------------------------------------------------------

zero :: Gfpx
zero = Gfpx {degree = -1, coeffMap = IntMap.empty}

one :: Gfpx
one = constant 1

negate :: Prime -> Gfpx -> Gfpx
negate _ f | isZero f = zero
negate p f = f {coeffMap = IntMap.map (Prime.negate p) (coeffMap f)}

add :: Prime -> Gfpx -> Gfpx -> Gfpx
add _ f g | isZero f = g
add _ f g | isZero g = f
add p f g | otherwise = fromNormCoeffMap c
  where
    c = IntMap.mergeWithKey addCoeff id id (coeffMap f) (coeffMap g)

    addCoeff _ fx gx = if x == 0 then Nothing else Just x
      where x = Prime.add p fx gx

sum :: Prime -> [Gfpx] -> Gfpx
sum p = foldr (add p) zero

subtract :: Prime -> Gfpx -> Gfpx -> Gfpx
subtract p f g = add p f (Factor.Gfpx.negate p g)

multiply :: Prime -> Gfpx -> Gfpx -> Gfpx
multiply p f g | lengthMonomials g < lengthMonomials f = multiply p g f
multiply _ f _ | isZero f = zero
multiply p f g | otherwise = IntMap.foldrWithKey fma zero (coeffMap f)
  where fma i c z = add p (multiplyPower i (multiplyConstant p c g)) z

square :: Prime -> Gfpx -> Gfpx
square p f = multiply p f f

product :: Prime -> [Gfpx] -> Gfpx
product p = foldr (multiply p) one

multiplyConstant :: Prime -> Gfp -> Gfpx -> Gfpx
multiplyConstant _ 0 _ = zero
multiplyConstant _ 1 f = f
multiplyConstant p c f =
    f {coeffMap = IntMap.map (Prime.multiply p c) (coeffMap f)}

multiplyPower :: Int -> Gfpx -> Gfpx
multiplyPower 0 f = f
multiplyPower i (Gfpx {degree = d, coeffMap = c}) =
    if d < 0 then zero
    else Gfpx {degree = d + i, coeffMap = IntMap.mapKeysMonotonic ((+) i) c}

multiplyExp :: Prime -> Gfpx -> Gfpx -> Integer -> Gfpx
multiplyExp _ z _ _ | isZero z = zero
multiplyExp _ z _ 0 = z
multiplyExp _ _ f _ | isZero f = zero
multiplyExp _ z f _ | isOne f = z
multiplyExp p z0 f0 k0 = go z0 f0 k0
  where
    go z _ 0 = z
    go z f k = go z' f' k'
      where
        z' = if even k then z else multiply p z f
        f' = square p f
        k' = k `div` 2

exp :: Prime -> Gfpx -> Integer -> Gfpx
exp p = multiplyExp p one

-------------------------------------------------------------------------------
-- Division
-------------------------------------------------------------------------------

division :: Prime -> Gfpx -> Gfpx -> (Gfpx,Gfpx)
division p f0 g = if gd < 0 then error "Gfpx.division by zero" else go zero f0
  where
    go q f = if d < 0 then (q,f) else go q' f'
      where
        fd = degree f
        d = fd - gd
        xd = monomial d (Prime.multiply p (powerCoeff f fd) gx)
        -- f - x^d*g = q*g + r ==> f = (q + x^d)*g + r
        q' = add p q xd
        f' = Factor.Gfpx.subtract p f (multiply p xd g)
    gd = degree g
    gx = Prime.invert p (powerCoeff g gd)

quotient :: Prime -> Gfpx -> Gfpx -> Gfpx
quotient p f g = fst $ Factor.Gfpx.division p f g

remainder :: Prime -> Gfpx -> Gfpx -> Gfpx
remainder p f g = snd $ Factor.Gfpx.division p f g

divides :: Prime -> Gfpx -> Gfpx -> Bool
divides p f g = isZero g || (not (isZero f) && isZero (remainder p g f))

-------------------------------------------------------------------------------
-- Every Euclidean domain a admits the definition of a greatest common
-- divisor function
--
--   egcd :: a -> a -> (a,(a,a))
--
-- such that if (g,(s,t)) = egcd x y then:
--
--   1. divides g x
--   2. divides g y
--   3. s*x + t*y == g
-------------------------------------------------------------------------------

egcd :: Prime -> Gfpx -> Gfpx -> (Gfpx,(Gfpx,Gfpx))
egcd p = go
  where
    go f g | isZero g =
        if isZero f then (zero,(zero,zero)) else (h, (constant x, zero))
      where
        x = Prime.invert p (leadingCoeff f)
        h = multiplyConstant p x f
    go f g | otherwise =
        (h, (t, Factor.Gfpx.subtract p s (multiply p q t)))
      where
        (q,r) = division p f g
        (h,(s,t)) = go g r

gcd :: Prime -> Gfpx -> Gfpx -> Gfpx
gcd p x y = fst $ egcd p x y

chineseRemainder :: Prime -> Gfpx -> Gfpx -> Gfpx -> Gfpx -> Gfpx
chineseRemainder p f g =
    \x y -> remainder p (add p (multiply p x tg) (multiply p y sf)) fg
  where
    (_,(s,t)) = egcd p f g
    fg = multiply p f g
    sf = multiply p s f
    tg = multiply p t g

-------------------------------------------------------------------------------
-- Polynomial composition
-------------------------------------------------------------------------------

compose :: Prime -> Gfpx -> Gfpx -> Gfpx
compose p f g = align 0 $ IntMap.foldrWithKey fma (0,zero) $ coeffMap f
  where
    fma i c z = (i, add p (align i z) (constant c))

    align i (d,z) = if k <= 0 then z else multiplyExp p z g (toInteger k)
      where k = d - i

-------------------------------------------------------------------------------
-- Ring operations modulo a nonzero polynomial f
-------------------------------------------------------------------------------

multiplyRemainder :: Prime -> Gfpx -> Gfpx -> Gfpx -> Gfpx
multiplyRemainder p f g h = remainder p (multiply p g h) f

squareRemainder :: Prime -> Gfpx -> Gfpx -> Gfpx
squareRemainder p f g = multiplyRemainder p f g g

multiplyExpRemainder :: Prime -> Gfpx -> Gfpx -> Gfpx -> Integer -> Gfpx
multiplyExpRemainder _ _ z _ _ | isZero z = zero
multiplyExpRemainder p f z _ 0 = remainder p z f
multiplyExpRemainder _ _ _ g _ | isZero g = zero
multiplyExpRemainder p f z g _ | isOne g = remainder p z f
multiplyExpRemainder p f z0 g0 k0 = go z0 g0 k0
  where
    go z _ 0 = z
    go z g k = go z' g' k'
      where
        z' = if even k then z else multiplyRemainder p f z g
        g' = squareRemainder p f g
        k' = k `div` 2

expRemainder :: Prime -> Gfpx -> Gfpx -> Integer -> Gfpx
expRemainder p f = multiplyExpRemainder p f one

-------------------------------------------------------------------------------
-- Finding all roots of a polynomial [Briggs1998, sec 4.2]
-------------------------------------------------------------------------------

roots :: Prime -> Gfpx -> [Gfp]
roots p | p < 3 = \f -> filter (\x -> evaluate p f x == 0) [0..(p-1)]
roots p | otherwise =
    \f -> if isLinear f then lin f
          else List.sort (go (Factor.Gfpx.gcd p f (xp f)))
  where
    go f | isLinear f = lin f
    go f | constantCoeff f == 0 = 0 : go (multiplyPower (-1) f)
    go f | otherwise =
        if 0 < d1 && d1 < degree f then go f1 ++ go f2
        else map (Prime.add p 1) (go (compose p f x1))
      where
        d1 = degree f1
        f1 = Factor.Gfpx.gcd p f (xp1 f)
        f2 = quotient p f f1

    lin f | isZero f = [0..(p-1)]
    lin f | isConstant f = []
    lin f | otherwise = [Prime.divide p (Prime.negate p b) a]  -- ax + b = 0
      where
        a = linearCoeff f
        b = constantCoeff f

    -- x^p - x == product [ (x - i) | 0 <= i < p ]
    xp f = Factor.Gfpx.subtract p (expRemainder p f variable p) variable

    -- x^p - x == x * (x^((p-1)/2) + 1) * (x^((p-1)/2) - 1)
    xp1 f = add p (expRemainder p f variable ((p - 1) `div` 2)) one

    -- x + 1
    x1 = add p (monomial 1 1) one

totallySplits :: Zx -> Prime -> Maybe [Gfp]
totallySplits f p = if length rs == Zx.degree f then Just rs else Nothing
  where rs = roots p (fromZx p f)

-------------------------------------------------------------------------------
-- A monic polynomial f of degree d is irreducible in GF(p)[x] if:
--
-- 1. f divides x^(p^d) - x
-- 2. For all prime divisors e of d, gcd (f, x^(p^(d/e)) - x) == 1
-------------------------------------------------------------------------------

irreducible :: Prime -> Gfpx -> Bool
irreducible p f =
    isLinear f ||
    (all (\e -> isOne (Factor.Gfpx.gcd p f (xpde e))) el &&
     divides p f (xpde 1))
  where
    d = toInteger (degree f)
    el = reverse (map fst (fst (Prime.trialDivision d)))

    -- x^(p^(d/e)) - x
    xpde e = Factor.Gfpx.subtract p (expRemainder p f variable pde) variable
      where pde = p ^ (d `div` e)

-------------------------------------------------------------------------------
-- Given a polynomial f in Z[x], use Hensel's Lemma to lift a root r
-- modulo p to a sequence of roots r_k modulo p^k.
-------------------------------------------------------------------------------

liftRoot :: Zx -> Prime -> Gfp -> [(Integer,Integer)]
liftRoot f p r = go p r
  where
     a = Prime.invert p (evaluate p (derivative p (fromZx p f)) r)
     go pk rk = (pk,rk) : go pk' rk'
       where
          pk' = pk * p
          rk' = (rk - evaluate pk' (fromZx pk' f) rk * a) `mod` pk'

-------------------------------------------------------------------------------
-- The Frobenius endomorphism
-------------------------------------------------------------------------------

frobenius :: Prime -> Gfpx -> Gfpx
frobenius _ f | isConstant f = f
frobenius p (Gfpx {degree = d, coeffMap = m}) =
    Gfpx {degree = d', coeffMap = m'}
  where
    d' = d * p'
    m' = IntMap.mapKeysMonotonic ((*) p') m
    p' = fromInteger p

frobeniusRange :: Prime -> Gfpx -> Bool
frobeniusRange p = all pDiv . IntMap.keys . coeffMap
  where
    p' = fromInteger p
    pDiv i = i `mod` p' == 0

-- Only defined for polynomials satisfying frobeniusRange
frobeniusInverse :: Prime -> Gfpx -> Gfpx
frobeniusInverse _ f | isConstant f = f
frobeniusInverse p (Gfpx {degree = d, coeffMap = m}) =
    Gfpx {degree = d', coeffMap = m'}
  where
    d' = d `div` p'
    m' = IntMap.mapKeysMonotonic pDiv m
    p' = fromInteger p
    pDiv i = if i `mod` p' == 0 then i `div` p'
             else error $ "power does not divide " ++ show p

-------------------------------------------------------------------------------
-- Square-free decomposition
--
-- https://en.wikipedia.org/wiki/Factorization_of_polynomials_over_finite_fields
-------------------------------------------------------------------------------

squareFree :: Prime -> Gfpx -> Bool
squareFree p f =
    if isZero f then error "GF(p)[x] square-free property not defined for zero"
    else isLinear f || isConstant (Factor.Gfpx.gcd p f (derivative p f))

squareFreeDecomposition :: Prime -> Gfpx -> [Gfpx]
squareFreeDecomposition _ f | isZero f =
    error "GF(p)[x] square-free decomposition not defined for zero"
squareFreeDecomposition _ f | isLinear f =
    [f]
squareFreeDecomposition p f | not (isMonic f) =
    case squareFreeDecomposition p g of
      [] -> error "GF(p)[x] square-free decomposition returned an empty list"
      a1 : al -> multiplyConstant p c a1 : al
  where
    (c,g) = constMonic p f
squareFreeDecomposition p f0 =
    output $ decompose f0
  where
    decompose f =
        if isOne cp then m
        else if isLinear cp then insert p' cp m
        else IntMap.union m (frob (decompose cp))
      where
        c = Factor.Gfpx.gcd p f (derivative p f)
        w = quotient p f c
        (cp,m) = loop c w 1 IntMap.empty

    loop c w _ m | isOne w = (frobeniusInverse p c, m)
    loop c w k m = loop (quotient p c y) y (k + 1) (insert k a m)
      where
        y = Factor.Gfpx.gcd p w c
        a = quotient p w y

    p' = fromInteger p

    frob = IntMap.mapKeysMonotonic ((*) p')

    insert _ a m | isOne a = m
    insert k a m = IntMap.insert k a m

    output m = map (\k -> IntMap.findWithDefault one k m) [1..d]
      where (d,_) = IntMap.findMax m

squareFreeRecomposition :: Prime -> [Gfpx] -> Gfpx
squareFreeRecomposition _ [] = error "GF(p)[x] square-free recomposition of empty list"
squareFreeRecomposition p al = fst $ foldr mult (one,one) al
  where mult a (f,g) = (multiply p g' f, g') where g' = multiply p a g

-------------------------------------------------------------------------------
-- Distinct degree factorization
--
-- Input:  Polynomial f assumed to be monic and square-free
-- Output: List of (g,d) where g is product of all monic irreducible degree d
--         factors of f
--
-- https://en.wikipedia.org/wiki/Factorization_of_polynomials_over_finite_fields
-------------------------------------------------------------------------------

factorDistinctDegree :: Prime -> Gfpx -> [(Gfpx,Int)]
factorDistinctDegree _ f | isZero f =
    error "GF(p)[x] distinct degree factorization not defined for zero"
factorDistinctDegree _ f | not (isMonic f) =
    error "GF(p)[x] distinct degree factorization requires monic input"
factorDistinctDegree p f0 =
    go 1 f0 variable
  where
    -- Invariant: degree f >= 2*d ==> x == remainder p (x^(p^(d-1))) f
    go d f _ | degree f < 2*d = if isOne f then [] else [(f, degree f)]
    go d f x | otherwise = if isOne g then go d' f x' else (g,d) : go d' f' x''
      where
        x' = expRemainder p f x p
        g = Factor.Gfpx.gcd p f (Factor.Gfpx.subtract p x' variable)
        d' = d + 1
        f' = quotient p f g
        x'' = remainder p x' f'

-------------------------------------------------------------------------------
-- Equal-degree factorization using the Cantor–Zassenhaus probabilistic algorithm
--
-- Input: Polynomial f assumed to be product of distinct monic irreducible
--        degree d polynomials
-- Output: List of degree d factors of f
--
-- https://en.wikipedia.org/wiki/Factorization_of_polynomials_over_finite_fields
-------------------------------------------------------------------------------

factorEqualDegree :: RandomGen r => Prime -> Gfpx -> Int -> r -> ([Gfpx],r)
factorEqualDegree _ f d r | degree f == d =
    ([f],r)
factorEqualDegree p _ _ _ | p == 2 =
    error "GF(2)[x] equal degree factorization not supported"
factorEqualDegree p f d r0 = go [] [f] r0
  where
    go dl [] r = (dl,r)
    go dl hl r = go (dl' ++ dl) hl' r'
      where
        (u,r') = uniform p n r
        v = Factor.Gfpx.subtract p (expRemainder p f u pd) one
        (dl',hl') = List.partition degreeD $ concatMap (split v) hl

    split v h =
        if isOne g || degree g == degree h then [h] else [g, quotient p h g]
      where
        g = Factor.Gfpx.gcd p v h

    degreeD h = degree h == d

    n = degree f
    pd = p ^ d

-------------------------------------------------------------------------------
-- Factorization of monic polynomials
--
-- Input:  Monic polynomial f
-- Output: List of irreducible polynomials g_i and positive integers k_i
--         such that f = product_i g_i^k_i
--
-- https://en.wikipedia.org/wiki/Factorization_of_polynomials_over_finite_fields
-------------------------------------------------------------------------------

factorSquareFree :: RandomGen r => Prime -> Gfpx -> r -> ([Gfpx],r)
factorSquareFree _ f r | isLinear f = ([f],r)
factorSquareFree p f r0 = foldr fed ([],r0) (factorDistinctDegree p f)
  where
    fed (h,d) (gl,r) = (gl' ++ gl, r')
      where (gl',r') = factorEqualDegree p h d r

factorMonic :: RandomGen r => Prime -> Gfpx -> r -> ([(Gfpx,Integer)],r)
factorMonic p f r0 = foldr fsf ([],r0) (zip (squareFreeDecomposition p f) [1..])
  where
    fsf (h,_) gkl_r | isOne h = gkl_r
    fsf (h,k) (gkl,r) = (map (\g -> (g,k)) gl ++ gkl, r')
      where (gl,r') = factorSquareFree p h r
