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

import Control.Monad (guard)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe (mapMaybe)

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

data PolynomialBase =
    FixedPolynomialBase Integer
  | ClosestPolynomialBase
  | FloorPolynomialBase
  deriving (Eq,Ord,Show)

data PolynomialCoeff =
    FixedPolynomialCoeff [Integer]
  | SmallestPolynomialCoeff
  | PositivePolynomialCoeff
  deriving (Eq,Ord,Show)

data PolynomialConfig =
    PolynomialConfig
      {polynomialDegree :: Int,
       polynomialBase :: PolynomialBase,
       polynomialCoeff :: PolynomialCoeff}
  deriving (Eq,Ord,Show)

defaultPolynomialConfig :: PolynomialConfig
defaultPolynomialConfig =
    PolynomialConfig
      {polynomialDegree = 3,
       polynomialBase = ClosestPolynomialBase,
       polynomialCoeff = SmallestPolynomialCoeff}

irreduciblePolynomial :: Zx -> Maybe Prime
irreduciblePolynomial f = List.find irred $ take 100 Prime.list
  where irred p = Gfpx.irreducible p (Gfpx.fromZx p f)

selectPolynomialBase :: PolynomialBase -> Integer -> Int -> Integer
selectPolynomialBase (FixedPolynomialBase m) _ _ = m
selectPolynomialBase ClosestPolynomialBase n d = nthRootClosest d n
selectPolynomialBase FloorPolynomialBase n d = nthRoot d n

selectPolynomialCoeff :: PolynomialCoeff -> Integer -> Int -> Integer -> [Integer]
selectPolynomialCoeff (FixedPolynomialCoeff c) _ _ _ = c
selectPolynomialCoeff cfg n d m = x : c
  where
    (x,c) = foldr reduce (n - last ms, [1]) (init ms)

    reduce mi (t,l) = (r, q : l)
      where (q,r) = idiv t mi

    ms = take d $ iterate ((*) m) m

    idiv = if cfg == PositivePolynomialCoeff then division else divisionClosest

selectPolynomial :: PolynomialConfig -> Integer -> (Zx,Integer)
selectPolynomial cfg n = (Zx.fromCoeff c, m)
  where
    d = polynomialDegree cfg
    m = selectPolynomialBase (polynomialBase cfg) n d
    c = selectPolynomialCoeff (polynomialCoeff cfg) n d m

-------------------------------------------------------------------------------
-- Finding smooth elements of Z[w]
-------------------------------------------------------------------------------

type FactorBase = [Prime]

isSmoothInteger :: FactorBase -> Integer -> Bool
isSmoothInteger _ n | abs n == 1 = True
isSmoothInteger [] _ = False
isSmoothInteger (p : ps) n = isSmoothInteger ps (snd (divPower p n))

notSmoothInteger :: FactorBase -> Integer -> Bool
notSmoothInteger fb = not . isSmoothInteger fb

rationalNorm :: Integer -> Nfzw -> Integer
rationalNorm = Nfzw.toInteger

algebraicNorm :: Zx -> Nfzw -> Integer
algebraicNorm = Nfzw.norm

isSmoothNfzw :: Zx -> Integer -> FactorBase -> FactorBase -> Nfzw -> Bool
isSmoothNfzw f m rfb afb x =
    isSmoothInteger rfb (rationalNorm m x) &&
    isSmoothInteger afb (algebraicNorm f x)

smoothNfzw :: Zx -> Integer -> FactorBase -> FactorBase -> [Nfzw]
smoothNfzw f m rfb afb = filter (isSmoothNfzw f m rfb afb) $ Nfzw.list

-------------------------------------------------------------------------------
-- Factor bases
-------------------------------------------------------------------------------

data FactorBaseConfig =
    FactorBaseConfig
      {minFactorBase :: Int,
       targetFactorBase :: (Int,Int),
       maxFactorBase :: Int}
  deriving (Eq,Ord,Show)

defaultFactorBaseConfig :: FactorBaseConfig
defaultFactorBaseConfig =
    FactorBaseConfig
      {minFactorBase = 10,
       targetFactorBase = (50,1000),
       maxFactorBase = 1000}

factorBase :: FactorBaseConfig -> (Nfzw -> Integer) -> FactorBase
factorBase cfg norm =
    ps1 ++ go ps2 (filter (notSmoothInteger ps1) norms)
  where
    go _ ns | trials - length ns >= successes = []
    go [] _ = []
    go (p : ps) ns = p : go ps (filter (notSmoothInteger [p]) ns)

    norms = map norm $ take trials Nfzw.list

    (ps1,ps2) = splitAt (minFactorBase cfg) (take (maxFactorBase cfg) Prime.list)

    (successes,trials) = targetFactorBase cfg

rationalFactorBase :: FactorBaseConfig -> Integer -> FactorBase
rationalFactorBase cfg m = factorBase cfg (Nfzw.toInteger m)

algebraicFactorBase :: FactorBaseConfig -> Zx -> FactorBase
algebraicFactorBase cfg f = factorBase cfg (Nfzw.norm f)

-------------------------------------------------------------------------------
-- Quadratic characters
-------------------------------------------------------------------------------

quadraticCharacters :: Zx -> [Nfzw] -> [Ideal] -> [Ideal]
quadraticCharacters f' xs = filter nonZeroChar
  where
    nonZeroChar i =
        Gfpx.evaluate q fq' s /= 0 &&
        all (\x -> not (Nfzw.inIdeal x i)) xs
      where
        fq' = Gfpx.fromZx q f'
        (s,q) = i

isQuadraticResidue :: Ideal -> Nfzw -> Bool
isQuadraticResidue (s,q) x =
    case jacobiSymbol (Nfzw.toInteger s x) q of
      Residue -> True
      ZeroResidue -> error "zero residue"
      NonResidue -> False

notQuadraticResidue :: Ideal -> Nfzw -> Bool
notQuadraticResidue i = not . isQuadraticResidue i

-------------------------------------------------------------------------------
-- Creating the matrix
-------------------------------------------------------------------------------

type Row = [Bool]

formRow :: Zx -> Integer -> [Prime] -> [Ideal] -> [Ideal] -> Nfzw -> Row
formRow f m rps aps qcs x =
    rationalRow rps (Nfzw.toInteger m x) ++
    algebraicRow f aps qcs x

rationalRow :: [Prime] -> Integer -> Row
rationalRow rps n =
    (n < 0) : snd (List.mapAccumL oddPower pks rps)
  where
    (pks,_) = Prime.factor rps (abs n)

algebraicRow :: Zx -> [Ideal] -> [Ideal] -> Nfzw -> Row
algebraicRow f aps qcs x =
    snd (List.mapAccumL oddPower iks aps) ++
    map (flip notQuadraticResidue x) qcs
  where
    (iks,_) = Nfzw.factor f aps x

oddPower :: Eq a => [(a,Int)] -> a -> ([(a,Int)],Bool)
oddPower ((p,k) : pks) q | p == q = (pks, odd k)
oddPower pks _ = (pks,False)

-------------------------------------------------------------------------------
-- Gaussian elimination
-------------------------------------------------------------------------------

gaussianElimination :: [Row] -> [[Int]]
gaussianElimination rows =
    map IntSet.toList $
    List.sortOn IntSet.size $
    List.foldl' processColumn ortho columns
  where
    ortho = map IntSet.singleton [0..(length rows - 1)]

    columns = map mkVec $ List.transpose rows

    processColumn basis column =
        case List.partition (evalVec column) basis of
          ([],_) -> basis
          (u : us, vs) -> map (addVec u) us ++ vs

    mkVec = IntSet.fromDistinctAscList . map fst . filter snd . zip [0..]

    evalVec u v  = odd (IntSet.size (IntSet.intersection u v))

    addVec u v = IntSet.difference (IntSet.union u v) (IntSet.intersection u v)

-------------------------------------------------------------------------------
-- Square roots
-------------------------------------------------------------------------------

rationalSquareRoot :: Integer -> Integer -> Zx -> [Prime] -> [Nfzw] -> Integer
rationalSquareRoot n m f' rps xs =
    Prime.product n (fm' : map sqrtPk pks)
  where
    fm' = Prime.fromInteger n (Zx.evaluate f' m)

    (pks,_) = Prime.factorProduct rps (map (Nfzw.toInteger m) xs)

    sqrtPk (p,k) =
        if odd k then error "prime power is not a square"
        else Prime.exp n (Prime.fromInteger n p) (toInteger (k `div` 2))

algebraicSquareRoot :: Integer -> Zx -> Integer -> Zx -> [Nfzw] -> [Integer]
algebraicSquareRoot n f m f' sq =
    map crtSqrt $
    concatMap allSigns $
    zip (iterate ((*) p) p) $
    List.transpose $
    map liftSqrt rcs
  where
    (p,rcs) = head $ mapMaybe splits (tail Prime.list)

    evalSquare pk x = Prime.product pk (fx2' : sqx)
      where
        fx2' = Prime.square pk (Gfpx.evaluate pk (Gfpx.fromZx pk f') x)
        sqx = map (Prime.fromInteger pk . Nfzw.toInteger x) sq

    splits q = do
        rs <- Gfpx.totallySplits f q
        let cs = map (sqrtModQ . evalSquare q) rs
        guard $ all ((/=) 0) cs
        return (q, zip rs cs)
      where
        sqrtModQ x | Prime.nonResidue q x = error "quadratic non-residue"
        sqrtModQ x | otherwise = Prime.sqrt q x

    liftSqrt (r,c) = zip (map snd rks) (snd $ List.mapAccumL lift c (tail rks))
      where
        lift ck (pk,rk) = ((ck - ((ck*ck - evalSquare pk rk) * a)) `mod` pk, ck)
        rks = Gfpx.liftRoot f p r
        a = Prime.invert p (Prime.multiply p 2 c)

    allSigns (_,[]) = error "no roots"
    allSigns (pk, rck : rcks) = map (\z -> (pk, rck : z)) $ foldr pm [[]] rcks
      where pm (rk,ck) z = map ((:) (rk,ck)) z ++ map ((:) (rk, pk - ck)) z

    crtSqrt (pk,rcks) =
        Prime.fromInteger n $
        Prime.toSmallestInteger pk $
        Prime.multiply pk (Prime.fromInteger pk n) $
        Prime.sum pk (map evalM rcks)
      where
        evalM (rk,ck) =
            Prime.multiply pk ck $
            Prime.invert pk (Prime.multiply pk m_rk frk')
          where
            m_rk = Prime.fromInteger pk (m - rk)
            frk' = Gfpx.evaluate pk (Gfpx.fromZx pk f') rk

-------------------------------------------------------------------------------
-- The number field sieve
-------------------------------------------------------------------------------

data Config =
    Config
      {polynomialConfig :: PolynomialConfig,
       rationalFactorBaseConfig :: FactorBaseConfig,
       algebraicFactorBaseConfig :: FactorBaseConfig,
       quadraticCharacterConfig :: Int,
       extraRankConfig :: Int}
  deriving (Eq,Ord,Show)

defaultConfig :: Config
defaultConfig =
    Config
      {polynomialConfig = defaultPolynomialConfig,
       rationalFactorBaseConfig = defaultFactorBaseConfig,
       algebraicFactorBaseConfig = defaultFactorBaseConfig,
       quadraticCharacterConfig = 20,
       extraRankConfig = 5}

factor :: Config -> Integer -> IO (Maybe Integer)
factor cfg n = do
    putStrLn $ "Attempting to factor n = " ++ show n
    putStrLn $ "NFS configuration = " ++ show cfg
    let (f,m) = selectPolynomial (polynomialConfig cfg) n
    putStrLn $ "Selected polynomial f = " ++ show f
    putStrLn $ "  such that f(m) = n where m = " ++ show m
    case irreduciblePolynomial f of
      Just p -> putStrLn $ "Verified that f is irreducible in Z[x] " ++
                           "(since it is irreducible in GF(" ++ show p ++
                           ")[x])"
      Nothing -> error $ "f does not appear to be irreducible in Z[x] " ++
                         "(use this fact to factor n)"
    let rfb = rationalFactorBase (rationalFactorBaseConfig cfg) m
    putStrLn $ "Rational factor base contains " ++ show (length rfb) ++
               " primes:" ++ abbrevList (map show rfb)
    let afb = algebraicFactorBase (algebraicFactorBaseConfig cfg) f
    let (apis,qpis) = span ((>=) (last afb) . snd) (Nfzw.ideals f)
    putStrLn $ "Algebraic factor base contains " ++ show (length apis) ++
               " first degree prime ideals:" ++ abbrevList (map show apis)
    let qcs = quadraticCharacterConfig cfg
    let extra = extraRankConfig cfg
    let cols = 1 + length rfb + length apis + qcs
    let xs = take (cols + extra) (smoothNfzw f m rfb afb)
    putStrLn $ "Searching for 1+" ++
               show (length rfb) ++ "+" ++
               show (length apis) ++ "+" ++
               show qcs ++ "+" ++
               show extra ++ " = " ++
               show (cols + extra) ++ " smooth elements of Z[w]:" ++
               abbrevList (map (\x -> show x ++ " |-> (" ++ show (rationalNorm m x) ++ ", " ++ show (algebraicNorm f x) ++ ")") xs)
    let f' = Zx.derivative f
    let qcl = take qcs (quadraticCharacters f' xs qpis)
    putStrLn $ "Generated " ++ show qcs ++ " quadratic characters:" ++
               abbrevList (map show qcl)
    let rows = map (formRow f m rfb apis qcl) xs
    let sql = map (map (\i -> xs !! i)) (gaussianElimination rows)
    putStrLn $ "Gaussian elimination resulted in " ++ show (length sql) ++
               " square products"
    let squareRoots [] = do
          putStrLn $ "No more square products, factorization failed"
          return Nothing
        squareRoots (sq : sqs) = do
          putStrLn $ "Considering square product " ++
                     (if length sq == 1 then
                        "consisting of a single element"
                      else
                        "of " ++ show (length sq) ++ " elements") ++ ":" ++
                     abbrevList (map show sq)
          let rsq = rationalSquareRoot n m f' rfb sq
          putStrLn $ "Rational square root is " ++ show rsq
          let sameSquare = (==) (Prime.square n rsq) . Prime.square n
          let (i,asq) = head $
                        filter (sameSquare . snd) $
                        zip ([0..] :: [Int]) $
                        algebraicSquareRoot n f m f' sq
          putStrLn $ "Element " ++ show i ++
                     " of candidate algebraic square roots has correct square"
          putStrLn $ "Algebraic square root is " ++ show asq
          let g = gcd n (rsq + asq)
          putStrLn $ "Greatest common divisor of n and " ++
                     "sum of square roots is " ++ show g
          if 1 < g && g < n then return (Just g) else squareRoots sqs
    squareRoots sql
