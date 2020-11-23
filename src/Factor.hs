{- |
module: Factor
description: Factoring integers and polynomials
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor
where

import qualified Data.List as List
import System.Random (RandomGen)
--import qualified System.Random as Random

import qualified Factor.Bz as Bz
import qualified Factor.Ec as Ec
import Factor.Gfpx (Gfpx)
import qualified Factor.Gfpx as Gfpx
import qualified Factor.Nfs as Nfs
import Factor.Prime (Prime,PrimePower)
import qualified Factor.Prime as Prime
import Factor.Term (Term(..))
import qualified Factor.Term as Term
import Factor.Util
import Factor.Value (Value(..))
--import qualified Factor.Value as Value
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- Factoring integers
-------------------------------------------------------------------------------

type IntegerFactorer r = Config -> Integer -> r -> Verbose ([PrimePower],r)

data Config =
    Config
      {trialDivisionConfig :: Integer,  -- Must be at least 3
       ecmConfig :: Ec.Config,
       nfsConfig :: Nfs.Config}
  deriving (Eq,Ord,Show)

defaultConfig :: Config
defaultConfig =
    Config
      {trialDivisionConfig = 1000,
       ecmConfig = Ec.defaultConfig,
       nfsConfig = Nfs.defaultConfig}

powerInteger :: Integer -> Integer -> Maybe (Integer,Integer)
powerInteger m n = go Prime.primes
  where
    go [] = error "ran out of primes"
    go (p : ps) =
        if r <= m then Nothing
        else if r ^ p /= n then go ps
        else case powerInteger m r of
               Nothing -> Just (r,p)
               Just (s,k) -> Just (s, p * k)
      where
        r = nthRoot p n

nfsFactorInteger :: RandomGen r => IntegerFactorer r
nfsFactorInteger cfg n r = do
    comment "Cranking up the number field sieve (NFS)"
    m <- Nfs.factor (nfsConfig cfg) n
    case m of
      Nothing -> error "NFS factorization failed"
      Just g -> do
        h <- pure $ n `div` g
        comment $ "NFS factorization: " ++ show g ++ " * " ++ show h
        mergeFactorInteger nfsFactorInteger cfg g h r

ecmFactorInteger :: RandomGen r => IntegerFactorer r
ecmFactorInteger cfg n r = do
    comment "Firing up the elliptic curve method (ECM)"
    (m,r') <- pure $ Ec.factor (ecmConfig cfg) n r
    case m of
      Nothing -> nfsFactorInteger cfg n r'
      Just g -> do
        h <- pure $ n `div` g
        comment $ "ECM factorization: " ++ show g ++ " * " ++ show h
        mergeFactorInteger ecmFactorInteger cfg g h r'

primeFactorInteger :: RandomGen r => IntegerFactorer r -> IntegerFactorer r
primeFactorInteger f cfg n r =
    case Prime.isPrime n r of
      (False,r') -> f cfg n r'
      (True,r') -> do
        comment $ "Prime: " ++ show n
        pure $ ([(n,1)],r')

powerFactorInteger :: RandomGen r => IntegerFactorer r -> IntegerFactorer r
powerFactorInteger _ _ 1 r = pure ([],r)
powerFactorInteger f cfg n r = do
    comment $ "Factor target is " ++ widthIntegerToString n
    case powerInteger (trialDivisionConfig cfg) n of
      Nothing -> primeFactorInteger f cfg n r
      Just (m,k) -> do
        comment $ "Factor target is perfect power: " ++ show m ++ "^" ++ show k
        comment $ "Adjusted factor target is " ++ widthIntegerToString m
        (pjs,r') <- primeFactorInteger f cfg m r
        pure $ (map (\(p,j) -> (p, j * k)) pjs, r')

mergeFactorInteger ::
    RandomGen r => IntegerFactorer r ->
    Config -> Integer -> Integer -> r -> Verbose ([PrimePower],r)
mergeFactorInteger f cfg m n r = do
    (pks,r') <- powerFactorInteger f cfg m r
    (pks',r'') <- powerFactorInteger f cfg n r'
    pure (Prime.multiplyPrimePowers pks pks', r'')

factorInteger :: RandomGen r => IntegerFactorer r
factorInteger _ n r | abs n <= 1 = pure ([(n,1)],r)
factorInteger cfg n r | n < 0 = do
    (pks,r') <- factorInteger cfg (-n) r
    pure ((-1,1) : pks, r')
factorInteger cfg n r = do
    comment $ "Attempting to factor " ++ widthIntegerToString n
    t <- pure $ trialDivisionConfig cfg
    ps <- pure $ takeWhile (\p -> p <= t) Prime.primes
    (pks,m) <- pure $ Prime.factor ps n
    comment $
      "Trial division up to " ++ show t ++ " found " ++
      (if null pks then "no factors"
       else let l = length pks in
            (if m == 1 then "all prime factors"
             else show l ++ " prime factor" ++ (if l == 1 then "" else "s")) ++
            ": " ++ List.intercalate " * "
                      (map (Term.toString . Term.fromPrimePower) pks))
    (pks',r') <- powerFactorInteger ecmFactorInteger cfg m r
    pure (pks ++ pks', r')

-------------------------------------------------------------------------------
-- Factoring polynomials over the integers
-------------------------------------------------------------------------------

factorZx :: Zx -> [(Zx,Integer)]
factorZx f | Zx.isConstant f = [(f,1)]
factorZx f = if n == 1 then hks else (Zx.constant n, 1) : hks
  where
    (c,gks) = Bz.factor f
    (mks,hks) = List.partition (Zx.isConstant . fst) gks
    n = List.foldr (\(m,k) z -> (Zx.constantCoeff m ^ k) * z) c mks

-------------------------------------------------------------------------------
-- Factoring polynomials over GF(p)
-------------------------------------------------------------------------------

factorGfpx :: RandomGen r => Prime -> Gfpx -> r -> ([(Gfpx,Integer)],r)
factorGfpx _ f r | Gfpx.isConstant f = ([(f,1)],r)
factorGfpx p f r = (if c == 1 then hs else (Gfpx.constant c, 1) : hs, r')
  where
    (hs,r') = Gfpx.factorMonic p g r
    (c,g) = Gfpx.constMonic p f

-------------------------------------------------------------------------------
-- Factoring expression values
-------------------------------------------------------------------------------

factorValue :: RandomGen r => Config -> Value -> r -> Verbose (Term,r)
factorValue cfg (ZValue n) r = do
    (pks,r') <- factorInteger cfg n r
    t <- pure $ Term.fromPrimePowers pks
    pure (t,r')
factorValue _ (ZxValue f x) r = pure (t,r)
  where
    gks = factorZx f
    t = Term.simplify $ Term.mkProduct $
        map (\(g,k) -> ExpTerm (Zx.toTerm x g) (IntegerTerm k)) gks
factorValue _ (GfpValue p a) r = pure (Term.fromGfp p a, r)
factorValue _ (GfpxValue p f x) r = pure (t,r')
  where
    (gks,r') = factorGfpx p f r
    t = flip Term.modulo p $ Term.simplify $ Term.mkProduct $
        map (\(g,k) -> ExpTerm (Gfpx.polyToTerm p x g) (IntegerTerm k)) gks

{-
let cfg = defaultConfig
let n = 4
r <- System.Random.getStdGen
factorInteger cfg n r
powerFactorInteger ecmFactorInteger cfg n r
-}
