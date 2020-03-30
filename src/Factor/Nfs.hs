{- |
module: Factor.Nfs
description: The general number field sieve
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Nfs
where

import qualified Data.IntSet as IntSet
import qualified Data.List as List

import qualified Factor.Gfpx as Gfpx
import Factor.Nfzw (Ideal,Nfzw(..))
import qualified Factor.Nfzw as Nfzw
import Factor.Prime (Prime)
import qualified Factor.Prime as Prime
import Factor.Util
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- Polynomial selection
--
-- Given n, return m and f such that f is monic, irreducible, and f(m) == n
-------------------------------------------------------------------------------

selectDegree :: Integer -> Int
selectDegree = const 4

irreduciblePolynomial :: Zx -> Bool
irreduciblePolynomial f = any irred $ take 100 Prime.list
  where irred p = Gfpx.irreducible p (Gfpx.fromZx p f)

selectPolynomialBase :: Bool -> Integer -> Int -> (Zx,Integer)
selectPolynomialBase pos n d = (Zx.fromCoeff (x : c), m)
  where
    (x,c) = foldr reduce (n - last ms, [1]) (init ms)

    reduce mi (t,l) = (r, q : l)
      where (q,r) = idiv t mi

    ms = take d $ iterate ((*) m) m
    m = root d n

    root = if pos then nthRoot else nthRootClosest
    idiv = if pos then division else divisionClosest

selectPolynomial :: Integer -> (Zx,Integer)
selectPolynomial n = selectPolynomialBase False n d
  where d = selectDegree n

-------------------------------------------------------------------------------
-- The ring homomorphism from Z[w] to Z, where w is a root of f
-------------------------------------------------------------------------------

nfzwToZ :: Integer -> Nfzw -> Integer
nfzwToZ m (Nfzw a b) = a + b*m

-------------------------------------------------------------------------------
-- Factor bases
-------------------------------------------------------------------------------

rationalFactorBase :: Integer -> [Prime]
rationalFactorBase b1 = takeWhile (\p -> p <= b1) Prime.list

algebraicFactorBase :: Integer -> Zx -> [Ideal]
algebraicFactorBase b2 f = takeWhile (\(_,p) -> p <= b2) (Nfzw.ideals f)

-------------------------------------------------------------------------------
-- Sieving
-------------------------------------------------------------------------------

sieve :: Zx -> Integer -> [Prime] -> [Ideal] ->
         Integer -> (Integer,Integer) -> [Nfzw]
sieve f m rps aps b (aMin,aMax) =
    filter smoothNfzw $ map (flip Nfzw b) $ filter (coprime b) [aMin..aMax]
  where
    smoothNfzw x = complete (Prime.factor rps (nfzwToZ m x)) &&
                   complete (Nfzw.factor f aps x)

    complete (_,s) = abs s == 1

smooth :: Zx -> Integer -> [Prime] -> [Ideal] -> (Integer,Integer) -> [Nfzw]
smooth f m rps aps aRange = concatMap (\b -> sieve f m rps aps b aRange) [1..]

-------------------------------------------------------------------------------
-- Quadratic characters
-------------------------------------------------------------------------------

quadraticCharacters :: Zx -> [Nfzw] -> Int -> [Ideal] -> [Ideal]
quadraticCharacters f' xs n = take n . filter nonZeroChar
  where
    nonZeroChar i =
        Gfpx.evaluate q fq' s /= 0 &&
        all (\x -> not (Nfzw.inIdeal x i)) xs
      where
        fq' = Gfpx.fromZx q f'
        (s,q) = i

-------------------------------------------------------------------------------
-- Creating the matrix
-------------------------------------------------------------------------------

type Row = [Bool]

-------------------------------------------------------------------------------
-- Gaussian elimination
-------------------------------------------------------------------------------

gaussianElimination :: [Row] -> [[Int]]
gaussianElimination rows =
    map IntSet.toList $ List.foldl' processColumn ortho columns
  where
    ortho = map IntSet.singleton [0..(length rows - 1)]

    columns = map mkVec $ List.transpose rows

    processColumn basis column =
        case List.partition (evalVec column) basis of
          (_,[]) -> basis
          (us, v : vs) -> us ++ map (addVec v) vs

    mkVec = IntSet.fromDistinctAscList . map fst . filter snd . zip [0..]

    evalVec u v  = even (IntSet.size (IntSet.difference v u))

    addVec u v = IntSet.difference (IntSet.union u v) (IntSet.intersection u v)

-------------------------------------------------------------------------------
-- Example
-------------------------------------------------------------------------------

{-
let n = 45113
let m = 31
let f = Zx.fromCoeff [8,29,15,1]
let f' = Zx.derivative f
let d = Zx.degree f
Zx.evaluate f m == n
irreduciblePolynomial f
let rps = rationalFactorBase 29
let aps = algebraicFactorBase 103 f
let phi = nfzwToZ m
let fac a b = (Prime.factor rps (phi x), Nfzw.factor f aps x) where x = Nfzw a b
let xs = take 40 (smooth f m rps aps (-1000,1000))
mapM_ (putStrLn . show) xs
quadraticCharacters f' xs 5 (drop (length aps) (Nfzw.ideals f))
-}
