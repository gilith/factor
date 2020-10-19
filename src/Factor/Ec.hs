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

addLambda :: Curve -> Gfp -> Gfp -> Gfp -> Gfp -> Point
addLambda e l x1 y1 x2 = Point x y
  where
    x = Prime.subtract k (Prime.square k l) (Prime.add k x1 x2)
    y = Prime.subtract k (Prime.multiply k l (Prime.subtract k x1 x)) y1
    k = kCurve e

doubleF :: Curve -> Point -> Factor Point
doubleF _ Infinity = Right Infinity
doubleF e (Point x y) = if y == 0 then Right Infinity else do
    l <- Prime.divideF k n d
    return $ addLambda e l x y x
  where
    n = Prime.add k (Prime.multiply k 3 (Prime.square k x)) a
    d = Prime.multiply k 2 y
    k = kCurve e
    a = aCurve e

double :: Curve -> Point -> Point
double e p = runFactor $ doubleF e p

addF :: Curve -> Point -> Point -> Factor Point
addF _ p1 Infinity = Right p1
addF _ Infinity p2 = Right p2
addF e p1 p2 =
    if x1 == x2 then
      if y1 == y2 then doubleF e p1 else Right Infinity
    else do
      l <- Prime.divideF k n d
      return $ addLambda e l x1 y1 x2
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

addMultiplyF :: Curve -> Point -> Point -> Integer -> Factor Point
addMultiplyF _ z _ 0 = Right z
addMultiplyF _ z Infinity _ = Right z
addMultiplyF e z p k = do
    z' <- if even k then return z else addF e z p
    p' <- doubleF e p
    addMultiplyF e z' p' k'
  where
    k' = k `div` 2

addMultiply :: Curve -> Point -> Point -> Integer -> Point
addMultiply e z p k = runFactor $ addMultiplyF e z p k

multiplyF :: Curve -> Point -> Integer -> Factor Point
multiplyF e = addMultiplyF e Infinity

multiply :: Curve -> Point -> Integer -> Point
multiply e p k = runFactor $ multiplyF e p k

-------------------------------------------------------------------------------
-- Lenstra's elliptic curve factorization algorithm
--
-- Input: An integer greater than 1 that is not divisible by 2 or 3
-- Output: Either a nontrivial factor of the input or failure

-- https://en.wikipedia.org/wiki/Lenstra_elliptic-curve_factorization
-------------------------------------------------------------------------------

factorCurve :: Curve -> Point -> [Prime] -> Maybe Integer
factorCurve e = go
  where
    go Infinity _ = Nothing
    go _ [] = Nothing
    go p (n : ns) =
        case multiplyF e p (pow n) of
          Left g -> Just g
          Right p' -> go p' ns

    pow n = last $ takeWhile (\i -> i < k) $ iterate ((*) n) 1
    k = kCurve e

factor :: RandomGen r => Integer -> r -> (Maybe Integer, r)
factor k r = (factorCurve e p Prime.list, r')
  where ((e,p),r') = uniformCurve k r

-------------------------------------------------------------------------------
-- Schoof's algorithm for counting points on the curve

-- https://en.wikipedia.org/wiki/Lenstra_elliptic-curve_factorization
-------------------------------------------------------------------------------

order :: Curve -> Integer
order = toInteger . length . points

traceOfFrobenius :: Curve -> Integer
traceOfFrobenius e = kCurve e + 1 - order e

{-
ghci Factor/Ec.hs

let e = Curve 5 3 4
let p1 = Point 3 0
let p2 = Point 3 0
let p3 = Point 0 2
add e (add e p1 p2) p3 == add e p1 (add e p2 p3)
points e

let n = 3119 * 4261
let n = 3119 * 3119
let r0 = Random.mkStdGen 91
factor n r0
let ((e,p),r1) = uniformCurve n r0
multiplyF e p (factorial 100)

let e = Curve 17 13 14
traceOfFrobenius e

-}
