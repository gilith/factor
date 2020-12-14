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

import qualified Factor.Bz as Bz
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

fixedPolynomialConfig :: Zx -> Integer -> PolynomialConfig
fixedPolynomialConfig f m =
    PolynomialConfig
      {polynomialDegree = FixedPolynomialDegree (Zx.degree f),
       polynomialBase = FixedPolynomialBase m,
       polynomialCoeff = FixedPolynomialCoeff (Zx.toCoeff f)}

selectPolynomialDegree :: PolynomialDegree -> Integer -> Int
selectPolynomialDegree (FixedPolynomialDegree d) _ = d
selectPolynomialDegree OptimalPolynomialDegree n =
    round $ (((3.0 * l) / log l) ** (1.0/3.0))
  where
    l = logInteger n

selectPolynomialBase :: PolynomialBase -> Integer -> Int -> Integer
selectPolynomialBase (FixedPolynomialBase m) _ _ = m
selectPolynomialBase ClosestPolynomialBase n d = nthRootClosest (toInteger d) n
selectPolynomialBase FloorPolynomialBase n d = nthRoot (toInteger d) n

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

oddPower :: Eq a => [(a,Integer)] -> a -> ([(a,Integer)],Bool)
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
    (p,rcs) = head $ mapMaybe splits (tail Prime.primes)

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
       extraRankConfig :: Int,
       verboseConfig :: Bool}
  deriving (Eq,Ord,Show)

defaultConfig :: Config
defaultConfig =
    Config
      {polynomialConfig = defaultPolynomialConfig,
       rationalFactorBaseConfig = OptimalFactorBase 3.0,
       algebraicFactorBaseConfig = OptimalFactorBase 10.0,
       quadraticCharacterConfig = 20,
       extraRankConfig = 5,
       verboseConfig = False}

setVerboseConfig :: Bool -> Config -> Config
setVerboseConfig v cfg = cfg {verboseConfig = v}

verboseList :: Config -> String -> [String] -> String
verboseList cfg s = if verboseConfig cfg then unabbrevList else abbrevList s

factorSquareRoots ::
    Config -> Integer -> Zx -> Integer -> FactorBase -> Zx -> [[Nfzw]] ->
    Verbose (Maybe Integer)
factorSquareRoots _ _ _ _ _ _ [] = do
    comment $ "No more square products, NFS factorization failed"
    pure Nothing
factorSquareRoots cfg n f m rfb f' (sq : sqs) = do
    comment $ "Considering square product " ++
              (if length sq == 1 then "consisting of a single element of Z[w]"
               else "of " ++ show (length sq) ++ " elements of Z[w]") ++
              ":" ++ verboseList cfg "elements" (map show sq)
    rsq <- pure $ rationalSquareRoot n m f' rfb sq
    comment $ "Rational square root is " ++ show rsq
    sameSquare <- pure $ (==) (Prime.square n rsq) . Prime.square n
    (i,asq) <- pure $ head $ filter (sameSquare . snd) $
               zip ([0..] :: [Int]) $ algebraicSquareRoot n f m f' sq
    comment $ "Element " ++ show i ++ " of candidate algebraic " ++
              "square roots has same square modulo n"
    comment $ "Algebraic square root is " ++ show asq
    g <- pure $ gcd n (rsq + asq)
    s <- pure $ 1 < g && g < n
    comment $ "Greatest common divisor of n and " ++
              "sum of square roots is " ++
              (if g == n then "n" else show g) ++
              (if s then "" else " (bad luck)")
    if s then pure (Just g) else factorSquareRoots cfg n f m rfb f' sqs

factorWithPolynomial ::
    Config -> Integer -> Zx -> Integer -> Verbose (Maybe Integer)
factorWithPolynomial cfg n f m = do
    rfm <- pure $ maxFactorBase (rationalFactorBaseConfig cfg) n
    rfb <- pure $ takeWhile ((>=) rfm) Prime.primes
    comment $ "Rational factor base contains " ++ show (length rfb) ++
              " prime integers:" ++ verboseList cfg "primes" (map show rfb)
    afm <- pure $ maxFactorBase (algebraicFactorBaseConfig cfg) n
    (ail,qil) <- pure $ span ((>=) afm . snd) (Nfzw.ideals f)
    afb <- pure $ map head $ List.group $ map snd ail
    comment $ "Algebraic factor base contains " ++ show (length ail) ++
              " first degree prime ideals:\n" ++
              "  (r,p) such that f(r) = 0 (mod p)" ++
              verboseList cfg "prime ideals" (map show ail)
    qcs <- pure $ quadraticCharacterConfig cfg
    extra <- pure $ extraRankConfig cfg
    cols <- pure $ 1 + length rfb + length ail + qcs
    xs <- pure $ take (cols + extra) (smoothNfzw f m rfb afb)
    comment $ "Searching for 1+" ++
              show (length rfb) ++ "+" ++
              show (length ail) ++ "+" ++
              show qcs ++ "+" ++
              show extra ++ " = " ++
              show (cols + extra) ++ " smooth elements of Z[w]:\n" ++
              "  a + bw |-> (a + bm, (-b)^degree(f) * f(a/(-b)))" ++
              verboseList cfg "smooth elements"
                (map (\x -> show x ++ " |-> (" ++
                            show (rationalNorm m x) ++ ", " ++
                            show (algebraicNorm f x) ++ ")") xs)
    f' <- pure $ Zx.derivative f
    comment $ "Derivative of f is f'(x) = " ++ show f'
    qcl <- pure $ take qcs (quadraticCharacters f' xs qil)
    comment $ "Generated " ++ show qcs ++ " quadratic characters " ++
              "nonzero for f' and all smooth elements:" ++
              verboseList cfg "quadratic characters" (map show qcl)
    rows <- pure $ map (formRow f m rfb ail qcl) xs
    sql <- pure $ map (map (\i -> xs !! i)) (gaussianElimination rows)
    comment $ "Gaussian elimination resulted in " ++ show (length sql) ++
              " square products"
    factorSquareRoots cfg n f m rfb f' sql

factor :: Config -> Integer -> Verbose (Maybe Integer)
factor cfg n = do
    comment $ "NFS configuration = " ++ show cfg
    comment $ "Attempting to factor n = " ++ show n
    (f,m) <- pure $ selectPolynomial (polynomialConfig cfg) n
    comment $ "Working in Z[w] where w is a complex root of f and f(m) = n"
    comment $ "  where f(x) = " ++ show f
    comment $ "  and m = " ++ show m
    case Bz.factor f of
      (1,[(_,1)]) -> do
          comment $ "Verified that f(x) is irreducible in Z[x]"
          factorWithPolynomial cfg n f m
      (_,gks) -> do
          comment $ "Factored f(x) in Z[x] as the product of:" ++ showProd gks
          comment $ "Evaluating at m factors n in Z as the product of:" ++
                    showProd (map evalFacAtM gks)
          if x < n then pure $ Just x else do
              comment $ "Adjust f(x) to " ++ show h
              factorWithPolynomial cfg n h m
        where
          (x,h) = maximum $ map absEvalAtM gks
          evalAtM g = Zx.evaluate g m
          absEvalAtM (g,_) = (abs (evalAtM g), g)
          evalFacAtM (g,k) = (Zx.constant (evalAtM g), k)
          showProd = concatMap (\gk -> "\n  " ++ showFac gk)
          showFac (g,1) = show g
          showFac (g,k) = "(" ++ show g ++ ") ^ " ++ show k

{-
ghci Nfs.hs
:break algebraicFactorBase
factor defaultConfig (3119 * 4261)
factor defaultConfig (48029 * 57641)
factor defaultConfig (3119 * 48029 * 57641)
factor defaultConfig (10712543 * 13777067)
factor defaultConfig (2616707501 * 3620408573)
-}
