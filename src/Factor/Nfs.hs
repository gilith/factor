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
import Data.Maybe (isNothing,mapMaybe)
--import Debug.Trace (trace)

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

data PolynomialDegree =
    FixedPolynomialDegree Int
  | OptimalPolynomialDegree
  deriving (Eq,Ord,Show)

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
      {polynomialDegree :: PolynomialDegree,
       polynomialBase :: PolynomialBase,
       polynomialCoeff :: PolynomialCoeff}
  deriving (Eq,Ord,Show)

defaultPolynomialConfig :: PolynomialConfig
defaultPolynomialConfig =
    PolynomialConfig
      {polynomialDegree = OptimalPolynomialDegree,
       polynomialBase = ClosestPolynomialBase,
       polynomialCoeff = SmallestPolynomialCoeff}

irreduciblePolynomial :: Zx -> Maybe Prime
irreduciblePolynomial f = List.find irred $ take 100 Prime.list
  where irred p = Gfpx.irreducible p (Gfpx.fromZx p f)

selectPolynomialDegree :: PolynomialDegree -> Integer -> Int
selectPolynomialDegree (FixedPolynomialDegree d) _ = d
selectPolynomialDegree OptimalPolynomialDegree n =
    round $ (((3.0 * l) / log l) ** (1.0/3.0))
  where
    l = logInteger n

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
    d = selectPolynomialDegree (polynomialDegree cfg) n
    m = selectPolynomialBase (polynomialBase cfg) n d
    c = selectPolynomialCoeff (polynomialCoeff cfg) n d m

-------------------------------------------------------------------------------
-- Factor bases
-------------------------------------------------------------------------------

{-
data FactorBaseConfig =
    FactorBaseConfig
      {trialsFactorBase :: Int,
       movingAverageFactorBase :: Int}
  deriving (Eq,Ord,Show)

defaultFactorBaseConfig :: FactorBaseConfig
defaultFactorBaseConfig =
    FactorBaseConfig
      {trialsFactorBase = 1000,
       movingAverageFactorBase = 10}

factorBase :: FactorBaseConfig -> (Nfzw -> Integer) -> [(Int,Prime)] -> FactorBase
factorBase cfg norm cps = take np (map snd cps)
  where
    (np,_) = nsl !! (g * (i + 1))
      where i = fromMaybe (length ds) (List.findIndex ((<) 0) ds)

    ds = difference $ movingAverage $ map pairs nsl

    nsl = compress $
          snd $
          List.mapAccumL testPrime (0,ns) cps

    ns = map norm $ take t $ drop t Nfzw.list

    testPrime (n,l) (c,p) = ((n',l'), (n', t - length l'))
      where
        n' = n + c
        l' = mapMaybe (destSmoothInteger [p]) l

    compress = dropWhile ((==) 0 . snd) .
               map last .
               List.groupBy (\(_,p) (_,q) -> p == q)

    pairs (n,s) = (toInteger n * toInteger t) `div` toInteger s

    movingAverage [] = []
    movingAverage l = sum a : movingAverage b
      where (a,b) = List.splitAt g l

    difference (x : y : z)  = (y - x) : difference (y : z)
    difference _ = []

    t = trialsFactorBase cfg
    g = movingAverageFactorBase cfg

rationalFactorBase :: FactorBaseConfig -> Integer -> FactorBase
rationalFactorBase cfg m = factorBase cfg (rationalNorm m) cps
  where cps = map ((,) 1) Prime.list

algebraicFactorBase :: FactorBaseConfig -> Zx -> [Ideal] -> FactorBase
algebraicFactorBase cfg f il = factorBase cfg (algebraicNorm f) cps
  where cps = map (\l -> (length l, head l)) $ List.group $ map snd $ il
-}

type FactorBase = [Prime]

data FactorBaseConfig =
    FixedFactorBase Integer
  | OptimalFactorBase Double
  deriving (Eq,Ord,Show)

defaultFactorBaseConfig :: FactorBaseConfig
defaultFactorBaseConfig = OptimalFactorBase 3.0

maxFactorBase :: FactorBaseConfig -> Integer -> Integer
maxFactorBase (FixedFactorBase b) _ = b
maxFactorBase (OptimalFactorBase c) n =
    round $ c * exp (t2**t2 * l**t1 * ll**t2)
  where
    t1 = 1.0 / 3.0
    t2 = 2.0 / 3.0
    l = logInteger n
    ll = log l

-------------------------------------------------------------------------------
-- Finding smooth elements of Z[w]
-------------------------------------------------------------------------------

destSmoothInteger :: FactorBase -> Integer -> Maybe Integer
destSmoothInteger _ n | abs n == 1 = Nothing
destSmoothInteger [] n = if n /= 0 && isSquare (abs n) then Nothing else Just n
destSmoothInteger (p : ps) n = destSmoothInteger ps (snd (divPower p n))

isSmoothInteger :: FactorBase -> Integer -> Bool
isSmoothInteger fb n = isNothing (destSmoothInteger fb n)

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
    Prime.product n (fm' : map sqrtPk pks ++ map sqrtS sl)
  where
    fm' = Prime.fromInteger n (Zx.evaluate f' m)

    (pks,sl) = Prime.factorProduct rps (map (Nfzw.toInteger m) xs)

    sqrtPk (p,k) =
        if odd k then error "prime power is not a square"
        else Prime.exp n (Prime.fromInteger n p) (toInteger (k `div` 2))

    sqrtS s = case destSquare (abs s) of
                Nothing -> error "smooth remainder is not a square"
                Just r -> r

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
--
-- Input: An odd integer greater than 5
-- Output: Either a nontrivial factor of the input or failure
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
       rationalFactorBaseConfig = OptimalFactorBase 3.0,
       algebraicFactorBaseConfig = OptimalFactorBase 10.0,
       quadraticCharacterConfig = 20,
       extraRankConfig = 5}

factor :: Config -> Integer -> IO (Maybe Integer)
factor cfg n = do
    putStrLn $ "NFS configuration = " ++ show cfg
    putStrLn $ "Attempting to factor " ++ show (widthInteger n) ++
               " bit integer n = " ++ show n
    let (f,m) = selectPolynomial (polynomialConfig cfg) n
    putStrLn $ "Working in Z[w] where w is a complex root of f and f(m) = n"
    putStrLn $ "  where f = " ++ show f
    putStrLn $ "  and m = " ++ show m
    case irreduciblePolynomial f of
      Just p -> putStrLn $ "Verified that f is irreducible in Z[x] " ++
                           "(since it is irreducible in GF(" ++ show p ++
                           ")[x])"
      Nothing -> error $ "f does not appear to be irreducible in Z[x] " ++
                         "(use this fact to factor n)"
    let rfm = maxFactorBase (rationalFactorBaseConfig cfg) n
    let rfb = takeWhile ((>=) rfm) Prime.list
    putStrLn $ "Rational factor base contains " ++ show (length rfb) ++
               " prime integers:" ++ abbrevList "primes" (map show rfb)
    let afm = maxFactorBase (algebraicFactorBaseConfig cfg) n
    let (ail,qil) = span ((>=) afm . snd) (Nfzw.ideals f)
    let afb = map head $ List.group $ map snd ail
    putStrLn $ "Algebraic factor base contains " ++ show (length ail) ++
               " first degree prime ideals:" ++
               abbrevList "prime ideals" (map show ail)
    let qcs = quadraticCharacterConfig cfg
    let extra = extraRankConfig cfg
    let cols = 1 + length rfb + length ail + qcs
    let xs = take (cols + extra) (smoothNfzw f m rfb afb)
    putStrLn $ "Searching for 1+" ++
               show (length rfb) ++ "+" ++
               show (length ail) ++ "+" ++
               show qcs ++ "+" ++
               show extra ++ " = " ++
               show (cols + extra) ++ " smooth elements of Z[w]:" ++
               abbrevList "smooth elements" (map (\x -> show x ++ " |-> (" ++ show (rationalNorm m x) ++ ", " ++ show (algebraicNorm f x) ++ ")") xs)
    let f' = Zx.derivative f
    putStrLn $ "Derivative of f is f' = " ++ show f'
    let qcl = take qcs (quadraticCharacters f' xs qil)
    putStrLn $ "Generated " ++ show qcs ++ " quadratic characters " ++
               "nonzero for f' and all smooth elements:" ++
               abbrevList "quadratic characters" (map show qcl)
    let rows = map (formRow f m rfb ail qcl) xs
    let sql = map (map (\i -> xs !! i)) (gaussianElimination rows)
    putStrLn $ "Gaussian elimination resulted in " ++ show (length sql) ++
               " square products"
    let squareRoots [] = do
          putStrLn $ "No more square products, factorization failed"
          return Nothing
        squareRoots (sq : sqs) = do
          putStrLn $ "Considering square product " ++
                     (if length sq == 1 then
                        "consisting of a single element of Z[w]"
                      else
                        "of " ++ show (length sq) ++ " elements of Z[w]") ++ ":" ++
                     abbrevList "elements" (map show sq)
          let rsq = rationalSquareRoot n m f' rfb sq
          putStrLn $ "Rational square root is " ++ show rsq
          let sameSquare = (==) (Prime.square n rsq) . Prime.square n
          let (i,asq) = head $
                        filter (sameSquare . snd) $
                        zip ([0..] :: [Int]) $
                        algebraicSquareRoot n f m f' sq
          putStrLn $ "Element " ++ show i ++ " of candidate algebraic " ++
                     "square roots has same square modulo n"
          putStrLn $ "Algebraic square root is " ++ show asq
          let g = gcd n (rsq + asq)
          let s = 1 < g && g < n
          putStrLn $ "Greatest common divisor of n and " ++
                     "sum of square roots is " ++
                     (if g == n then "n" else show g) ++
                     (if s then "" else " (bad luck)")
          if s then return (Just g) else squareRoots sqs
    squareRoots sql

{-
ghci Nfs.hs
:break algebraicFactorBase
factor defaultConfig (3119 * 4261)
factor defaultConfig (48029 * 57641)
factor defaultConfig (3119 * 48029 * 57641)
factor defaultConfig (10712543 * 13777067)
factor defaultConfig (2616707501 * 3620408573)
-}
