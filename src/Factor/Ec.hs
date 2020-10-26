{- |
module: Factor.Ec
description: Elliptic curve factorization and primality proving
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Ec
where

--import Control.Monad (filterM)
--import qualified Data.List as List
import System.Random (RandomGen)
import qualified System.Random as Random

import Factor.Gfpx (Gfpx)
import qualified Factor.Gfpx as Gfpx
import Factor.Prime (Prime,Gfp)
import qualified Factor.Prime as Prime
import Factor.Util
import Factor.Zx ()
--import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- Elliptic curves
-------------------------------------------------------------------------------

data Curve =
    Curve {kCurve :: Prime, aCurve :: Gfp, bCurve :: Gfp}
  deriving (Eq,Ord)

data Point =
    Point {xPoint :: Gfp, yPoint :: Gfp}
  | Infinity
  deriving (Eq,Ord)

instance Show Curve where
  show e = "y^2 = " ++ show f ++ " (mod " ++ show k ++ ")"
    where
      f = Gfpx.toSmallestZx k (rhs e)
      k = kCurve e

instance Show Point where
  show Infinity = "infinity"
  show (Point x y) = "(" ++ show x ++ "," ++ show y ++ ")"

rhs :: Curve -> Gfpx
rhs e = Gfpx.fromCoeff [bCurve e, aCurve e, 0, 1]

rhsEvaluate :: Curve -> Gfp -> Gfp
rhsEvaluate e = Gfpx.evaluate (kCurve e) (rhs e)

-------------------------------------------------------------------------------
-- Points on the curve
-------------------------------------------------------------------------------

onCurve :: Curve -> Point -> Bool
onCurve _ Infinity = True
onCurve e (Point x y) = Prime.square (kCurve e) y == rhsEvaluate e x

xPoints :: Curve -> Gfp -> [Point]
xPoints e x =
    case jacobiSymbol y2 k of
      NonResidue -> []
      ZeroResidue -> [Point x 0]
      Residue -> [Point x y, Point x y']
  where
    y2 = rhsEvaluate e x
    y = Prime.sqrt k y2
    y' = Prime.negate k y
    k = kCurve e

points :: Curve -> [Point]
points e = Infinity : concatMap (xPoints e) (Prime.elements (kCurve e))

-------------------------------------------------------------------------------
-- Discriminant
-------------------------------------------------------------------------------

discriminant :: Curve -> Gfp
discriminant (Curve k a b) =
    Prime.multiply k (Prime.fromInteger k (-16)) s
  where
    s = Prime.add k s1 s2
    s1 = Prime.multiply k (Prime.fromInteger k 4) (Prime.cube k a)
    s2 = Prime.multiply k (Prime.fromInteger k 27) (Prime.square k b)

singular :: Curve -> Bool
singular = (==) 0 . discriminant

-------------------------------------------------------------------------------
-- Generating a random elliptic curve and (finite) point on the curve
--
-- https://en.wikipedia.org/wiki/Elliptic_curve_primality
-------------------------------------------------------------------------------

uniformCurve :: RandomGen r => Prime -> r -> ((Curve,Point),r)
uniformCurve k | k <= 3 = error "fields cannot have characteristic 2 or 3"
uniformCurve k = pick
  where
    pick r0 = if singular e then pick r3 else ((e, Point x y), r3)
      where
        (a,r1) = Prime.uniform k r0
        (x,r2) = Prime.uniform k r1
        (y,r3) = Prime.uniform k r2
        x2 = Prime.square k x
        y2 = Prime.square k y
        b = Prime.subtract k y2 (Prime.multiply k x (Prime.add k x2 a))
        e = Curve k a b

uniformPoint :: RandomGen r => Curve -> r -> (Point,r)
uniformPoint e = pick
  where
    k = kCurve e

    pick r0 =
        case ps of
          [] -> pick r1
          [p] -> (p,r1)
          [p,p'] -> (if n then p' else p, r2)
          _ -> error "more than 2 points for a fixed x value"
      where
        (x,r1) = Prime.uniform k r0
        ps = xPoints e x
        (n,r2) = Random.random r1

-------------------------------------------------------------------------------
-- Point negation
--
-- https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication
-------------------------------------------------------------------------------

negate :: Curve -> Point -> Point
negate _ Infinity = Infinity
negate (Curve k _ _) (Point x y) = Point x (Prime.negate k y)

-------------------------------------------------------------------------------
-- Point addition
--
-- https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication
-------------------------------------------------------------------------------

addLambdaF :: Curve -> Gfp -> Gfp -> Gfp -> Gfp -> Gfp -> Factor Integer Point
addLambdaF e n d x1 y1 x2 = do
    l <- Prime.divideF k n d
    let x = Prime.subtract k (Prime.square k l) (Prime.add k x1 x2)
    let y = Prime.subtract k (Prime.multiply k l (Prime.subtract k x1 x)) y1
    return $ Point x y
  where
    k = kCurve e

doubleF :: Curve -> Point -> Factor Integer Point
doubleF _ Infinity = Right Infinity
doubleF e (Point x y) =
    if y == 0 then Right Infinity else addLambdaF e n d x y x
  where
    n = Prime.add k
          (Prime.multiply k (Prime.fromInteger k 3) (Prime.square k x)) a
    d = Prime.multiply k (Prime.fromInteger k 2) y
    k = kCurve e
    a = aCurve e

double :: Curve -> Point -> Point
double e p = runFactor $ doubleF e p

addF :: Curve -> Point -> Point -> Factor Integer Point
addF _ p1 Infinity = Right p1
addF _ Infinity p2 = Right p2
addF e p1 p2 =
    if x1 /= x2 then addLambdaF e n d x1 y1 x2
    else if y1 == y2 then doubleF e p1
    else Right Infinity
  where
    n = Prime.subtract k y2 y1
    d = Prime.subtract k x2 x1
    Point x1 y1 = p1
    Point x2 y2 = p2
    k = kCurve e

add :: Curve -> Point -> Point -> Point
add e p1 p2 = runFactor $ addF e p1 p2

-------------------------------------------------------------------------------
-- Point multiplication
--
-- https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication
-------------------------------------------------------------------------------

addMultiplyF :: Curve -> Point -> Point -> Integer -> Factor Integer Point
addMultiplyF _ z _ 0 = Right z
addMultiplyF e z p n | n < 0 = addMultiplyF e z (Factor.Ec.negate e p) (-n)
addMultiplyF _ z Infinity _ = Right z
addMultiplyF e z p n = do
    z' <- if even n then return z else addF e z p
    p' <- doubleF e p
    addMultiplyF e z' p' n'
  where
    n' = n `div` 2

addMultiply :: Curve -> Point -> Point -> Integer -> Point
addMultiply e z p n = runFactor $ addMultiplyF e z p n

multiplyF :: Curve -> Point -> Integer -> Factor Integer Point
multiplyF e = addMultiplyF e Infinity

multiply :: Curve -> Point -> Integer -> Point
multiply e p n = runFactor $ multiplyF e p n

-------------------------------------------------------------------------------
-- Lenstra's elliptic curve factorization algorithm
--
-- Input: An integer greater than 1 that is not divisible by 2 or 3
-- Output: Either a nontrivial factor of the input or failure
--
-- https://en.wikipedia.org/wiki/Lenstra_elliptic-curve_factorization
-------------------------------------------------------------------------------

data CurvesConfig =
    FixedCurvesConfig Int
  | OptimalCurvesConfig
  deriving (Eq,Ord,Show)

data Config =
    Config
      {curvesConfig :: CurvesConfig}
  deriving (Eq,Ord,Show)

defaultCurvesConfig :: CurvesConfig
defaultCurvesConfig = OptimalCurvesConfig

evalCurvesConfig :: CurvesConfig -> Integer -> Int
evalCurvesConfig (FixedCurvesConfig n) _ = n
evalCurvesConfig OptimalCurvesConfig n = 10 + w*w
  where w = widthInteger n `div` 5

defaultConfig :: Config
defaultConfig =
    Config
      {curvesConfig = defaultCurvesConfig}

factorPrime :: Prime -> [(Curve,Point)] -> Factor Integer [(Curve,Point)]
factorPrime _ [] = return []
factorPrime q eps = filter fin <$> mapM fac eps
  where
    fac (e,p) = ((,) e) <$> multiplyF e p n
    fin (_,p) = p /= Infinity
    n = last $ takeWhile (\i -> i < k) $ iterate ((*) q) 1
    k = kCurve $ fst $ head eps

factorPrimes :: [Prime] -> [(Curve,Point)] -> Maybe Integer
factorPrimes [] _ = Nothing
factorPrimes _ [] = Nothing
factorPrimes (q : qs) eps =
    case factorPrime q eps of
      Left g -> Just g
      Right eps' -> factorPrimes qs eps'

factor :: RandomGen r => Config -> Integer -> r -> (Maybe Integer, r)
factor cfg k r = (factorPrimes Prime.list eps, r')
  where
    (eps,r') = unfoldrN (uniformCurve k) n r
    n = evalCurvesConfig (curvesConfig cfg) k

-------------------------------------------------------------------------------
-- Division polynomials
--
-- https://en.wikipedia.org/wiki/Division_polynomials
-- https://math.mit.edu/classes/18.783/2019/LectureNotes6.pdf
-------------------------------------------------------------------------------

data DivisionPolynomial =
    DivisionPolynomial
      {psiDivisionPolynomial :: Gfpx,    -- if n is even multiply psi_n by 2y
       phiDivisionPolynomial :: Gfpx,
       omegaDivisionPolynomial :: Gfpx}  -- if n is odd multiply omega_n by y
  deriving (Eq,Ord,Show)

psiDivisionPolynomials :: Curve -> [Gfpx]
psiDivisionPolynomials e = p_0 : p_2n_1 True p_1 p_2 p_3 p_4 []
  where
    p_0 = Gfpx.zero
    p_1 = Gfpx.one
    p_2 = Gfpx.one
    p_3 = Gfpx.fromCoeff
            [Prime.negate k (Prime.square k a),
             Prime.multiply k (Prime.fromInteger k 12) b,
             Prime.multiply k (Prime.fromInteger k 6) a,
             0,
             Prime.fromInteger k 3]
    p_4 = Gfpx.fromCoeff
            [Prime.subtract k
               (Prime.multiply k (Prime.fromInteger k (-2)) (Prime.cube k a))
               (Prime.multiply k (Prime.fromInteger k 16) (Prime.square k b)),
             Prime.multiply k (Prime.fromInteger k (-8)) (Prime.multiply k a b),
             Prime.multiply k (Prime.fromInteger k (-10)) (Prime.square k a),
             Prime.multiply k (Prime.fromInteger k 40) b,
             Prime.multiply k (Prime.fromInteger k 10) a,
             0,
             Prime.fromInteger k 2]

    p_2n_1 nEven p_n_m1 p_n p_n_1 p_n_2 p_rest =
        p_2n (not nEven) p_n_m1 p_n p_n_1 p_n_2 p_n_3 p_rest'
      where
        (p_n_3,p_rest') = case p_rest of
                            [] -> (p,[])
                            p_h : p_t -> (p_h, p_t ++ [p])
        p = if nEven then Gfpx.subtract k (Gfpx.multiply k f2 s) t
            else Gfpx.subtract k s (Gfpx.multiply k f2 t)
        s = Gfpx.multiply k p_n_2 (Gfpx.cube k p_n)
        t = Gfpx.multiply k p_n_m1 (Gfpx.cube k p_n_1)

    p_2n nEven p_n_m2 p_n_m1 p_n p_n_1 p_n_2 p_rest =
        p_n_m2 : p_2n_1 nEven p_n_m1 p_n p_n_1 p_n_2 (p_rest ++ [p])
      where
        p = Gfpx.multiply k p_n (Gfpx.subtract k s t)
        s = Gfpx.multiply k p_n_2 (Gfpx.square k p_n_m1)
        t = Gfpx.multiply k p_n_m2 (Gfpx.square k p_n_1)

    k = kCurve e
    a = aCurve e
    b = bCurve e
    f = Gfpx.multiplyConstant k (Prime.fromInteger k 4) (rhs e)
    f2 = Gfpx.square k f

divisionPolynomials :: Curve -> [DivisionPolynomial]
divisionPolynomials e =
    case psiDivisionPolynomials e of
      p_0 : p_1 : p_2 : p_rest ->
        lift True (Gfpx.negate k p_2) (Gfpx.negate k p_1) p_0 p_1 (p_2 : p_rest)
      _ -> error "not enough psi division polynomials"
  where
    lift _ _ _ _ _ [] = error "ran out of psi division polynomials"
    lift nEven psi_n_m2 psi_n_m1 psi_n psi_n_1 (psi_n_2 : psi_rest) =
        p_n : lift (not nEven) psi_n_m1 psi_n psi_n_1 psi_n_2 psi_rest
      where
        p_n = DivisionPolynomial
                {psiDivisionPolynomial = psi_n,
                 phiDivisionPolynomial = phi_n,
                 omegaDivisionPolynomial = omega_n}

        phi_n = if nEven then Gfpx.subtract k (Gfpx.multiply k f s) t
                else Gfpx.subtract k s (Gfpx.multiply k f t)
          where
            s = Gfpx.multiply k Gfpx.variable (Gfpx.square k psi_n)
            t = Gfpx.multiply k psi_n_1 psi_n_m1

        omega_n = if nEven then Gfpx.multiplyConstant k h p else p
          where
            p = Gfpx.subtract k s t
            s = Gfpx.multiply k psi_n_2 (Gfpx.square k psi_n_m1)
            t = Gfpx.multiply k psi_n_m2 (Gfpx.square k psi_n_1)

    k = kCurve e
    h = Prime.invert k (Prime.fromInteger k 2)
    f = Gfpx.multiplyConstant k (Prime.fromInteger k 4) (rhs e)

-------------------------------------------------------------------------------
-- Endomorphisms of curve points
--
-- https://math.mit.edu/classes/18.783/2019/LectureNotes9.pdf
-------------------------------------------------------------------------------

data End = End Gfpx Gfpx
  deriving (Eq,Ord)

instance Show End where
  show (End x y) = "(" ++ show x ++ ", " ++ show_y y ++ ")"
    where
      show_y f | Gfpx.isZero f = "0"
      show_y f | Gfpx.isOne f = "y"
      show_y f | Gfpx.lengthMonomials f == 1 = show f ++ "y"
      show_y f = "(" ++ show f ++ ")y"

evaluateEnd :: Curve -> End -> Point -> Point
evaluateEnd _ _ Infinity = error "cannot evaluate endomorphism at infinity"
evaluateEnd e (End f g) (Point x y) =
    Point (Gfpx.evaluate k f x) (Prime.multiply k (Gfpx.evaluate k g x) y)
  where
    k = kCurve e

identityEnd :: Curve -> Gfpx -> End
identityEnd e h = End (Gfpx.remainder (kCurve e) Gfpx.variable h) Gfpx.one

composeEnd :: Curve -> Gfpx -> End -> End -> End
composeEnd e h (End x1 y1) (End x2 y2) = End x y
  where
    x = Gfpx.composeRemainder k h x1 x2
    y = Gfpx.multiplyRemainder k h (Gfpx.composeRemainder k h y1 x2) y2
    k = kCurve e

negateEnd :: Curve -> End -> End
negateEnd e (End x y) = End x (Gfpx.negate (kCurve e) y)

addLambdaEnd :: Curve -> Gfpx -> Gfpx -> Gfpx -> Gfpx -> Gfpx -> Gfpx -> Factor Gfpx End
addLambdaEnd e h n d x1 y1 x2 = do
    l <- Gfpx.divideRemainderF k h n d
    let x = Gfpx.subtract k
              (Gfpx.multiplyRemainder k h (Gfpx.squareRemainder k h l) f)
              (Gfpx.add k x1 x2)
    let y = Gfpx.subtract k
              (Gfpx.multiplyRemainder k h l (Gfpx.subtract k x1 x)) y1
    return $ End x y
  where
    f = Gfpx.remainder k (rhs e) h
    k = kCurve e

doubleEnd :: Curve -> Gfpx -> End -> Factor Gfpx End
doubleEnd e h (End x y) = addLambdaEnd e h n d x y x
  where
    n = Gfpx.add k
          (Gfpx.multiplyConstant k
             (Prime.fromInteger k 3)
             (Gfpx.squareRemainder k h x))
          (Gfpx.constant a)
    d = Gfpx.multiplyConstant k
          (Prime.fromInteger k 2)
          (Gfpx.multiplyRemainder k h y f)
    f = Gfpx.remainder k (rhs e) h
    k = kCurve e
    a = aCurve e

addEnd:: Curve -> Gfpx -> End -> End -> Factor Gfpx End
addEnd e h p1 p2 =
    if x1 /= x2 then addLambdaEnd e h n d x1 y1 x2
    else if y1 == y2 then doubleEnd e h p1
    else error "adding a point and its negation"
  where
    n = Gfpx.subtract k y2 y1
    d = Gfpx.subtract k x2 x1
    End x1 y1 = p1
    End x2 y2 = p2
    k = kCurve e

addMultiplyEnd :: Curve -> Gfpx -> End -> End -> Integer -> Factor Gfpx End
addMultiplyEnd _ _ z _ 0 = Right z
addMultiplyEnd e h z p n | n < 0 =
    addMultiplyEnd e h z (Factor.Ec.negateEnd e p) (-n)
addMultiplyEnd e h z p n = do
    z' <- if even n then return z else addEnd e h z p
    p' <- doubleEnd e h p
    addMultiplyEnd e h z' p' n'
  where
    n' = n `div` 2

multiplyEnd :: Curve -> Gfpx -> End -> Integer -> Factor Gfpx End
multiplyEnd _ _ _ 0 = error "scalar multiply by zero"
multiplyEnd e h p n = addMultiplyEnd e h p p (n - 1)

frobeniusEnd :: Curve -> Gfpx -> End
frobeniusEnd e h = End x y
  where
    x = Gfpx.expRemainder k h (Gfpx.remainder k Gfpx.variable h) k
    y = Gfpx.expRemainder k h f ((k - 1) `div` 2)
    f = Gfpx.remainder k (rhs e) h
    k = kCurve e

-------------------------------------------------------------------------------
-- Schoof's algorithm for counting points on the curve
--
-- https://en.wikipedia.org/wiki/Schoof%27s_algorithm
-- https://math.mit.edu/classes/18.783/2019/LectureNotes9.pdf
-------------------------------------------------------------------------------

traceOfFrobeniusMod2 :: Curve -> Integer
traceOfFrobeniusMod2 e = if even (length (Gfpx.roots k f)) then 1 else 0
  where
    f = rhs e
    k = kCurve e

traceOfFrobeniusModOddPrime :: Curve -> Prime -> Gfpx -> Integer
traceOfFrobeniusModOddPrime e l = go
  where
    go h = case tr h of
             Left g -> if Gfpx.degree g < Gfpx.degree h then go g
                       else error "not a proper factor"
             Right n -> n

    tr h = do
        kl <- multiplyEnd e h (identityEnd e h) (k `mod` l)
        if kl == negateEnd e pil2 then return 0 else do
          pil2_kl <- addEnd e h pil2 kl
          let inc c _ | c == l = error $ "couldn't find trace mod " ++ show l
              inc c cpil | cpil == pil2_kl = return c
              inc c cpil = addEnd e h pil cpil >>= inc (c + 1)
          inc 1 pil
      where
        pil2 = composeEnd e h pil pil
        pil = frobeniusEnd e h

    k = kCurve e

traceOfFrobenius :: Curve -> Integer
traceOfFrobenius e = go (traceOfFrobeniusMod2 e, 2) (tail Prime.list)
  where
    go (t,m) _ | b <= m = Prime.toSmallestInteger m t
    go _ [] = error "ran out of primes"
    go tm (l : ls) | l == k = go tm ls
    go (t,m) (l : ls) = go (t',m') ls
      where
        tl = traceOfFrobeniusModOddPrime e l (psi !! fromInteger l)
        t' = chineseRemainder l m tl t
        m' = l * m

    psi = psiDivisionPolynomials e
    b = 2 * nthRoot 2 (4 * k) + 1  -- Number of possible values of trace
    k = kCurve e

supersingular :: Curve -> Bool
supersingular = (==) 0 . traceOfFrobenius

order :: Curve -> Integer
order e = kCurve e + 1 - traceOfFrobenius e

{-
ghci Factor/Ec.hs

let e = Curve 5 3 4
let p1 = Point 3 0
let p2 = Point 3 0
let p3 = Point 0 2
add e (add e p1 p2) p3 == add e p1 (add e p2 p3)
points e

let cfg = defaultConfig
let n = 3119 * 4261
let n = 3119 * 3119
let n = 48029 * 57641
let n = 3119 * 48029 * 57641
let n = 10712543 * 13777067
let n = 2616707501 * 3620408573
let n = 2616707501 ^ 2
let r0 = Random.mkStdGen 90
evalCurvesConfig (curvesConfig cfg) n
factor cfg n r0

let e = Curve 17 13 14
let e = Curve 5 3 4
let e = Curve 7 5 5
let l = (3 :: Integer)
let k = kCurve e
let (_,h) = Gfpx.constMonic k (psiDivisionPolynomials e !! fromInteger l)
traceOfFrobeniusModOddPrime e l h
let pil = frobeniusEnd e h
let pil2 = composeEnd e h pil pil
let Right kl = multiplyEnd e h (identityEnd e h) (k `mod` l)
kl == negateEnd e pil2
addEnd e h pil2 kl
let Right pil2_kl = it
let Left h = it
traceOfFrobenius e
order e

let k = 2616707501
let k = 48029
let r0 = Random.mkStdGen 35
let ((e,p),r1) = uniformCurve k r0
let psi = psiDivisionPolynomials e
let psi_l l = snd (Gfpx.constMonic k (psi !! fromInteger l))
mapM_ (putStrLn . show . (\l -> let h = psi_l l in (traceOfFrobeniusModOddPrime e l h, l, Gfpx.degree h))) (tail Prime.list)
mapM_ (putStrLn . show . (\l -> let h = psi_l l in (l, Gfpx.degree h, head (fst (Gfpx.factorMonic k h r1))))) (tail Prime.list)
-}
