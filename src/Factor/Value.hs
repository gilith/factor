{- |
module: Factor.Value
description: Expression values
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Value
where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Factor.Gfpx (Gfpx)
import qualified Factor.Gfpx as Gfpx
import Factor.Prime (Gfp,Prime)
import qualified Factor.Prime as Prime
import Factor.Term (Term(..),Var)
import qualified Factor.Term as Term
import Factor.Zx (Zx)
import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- Values
-------------------------------------------------------------------------------

data Value =
    ZValue Integer
  | ZxValue Zx Var
  | GfpValue Prime Gfp
  | GfpxValue Prime Gfpx Var
  deriving (Eq,Ord,Show)

free :: Value -> Set Var
free (ZxValue _ x) = Set.singleton x
free (GfpxValue _ _ x) = Set.singleton x
free _ = Set.empty

normalize :: Value -> Value
normalize (ZxValue f _) | Zx.isConstant f =
    ZValue (Zx.constantCoeff f)
normalize (GfpxValue p f _) | Gfpx.isConstant f =
    GfpValue p (Gfpx.constantCoeff f)
normalize v = v

negate :: Value -> Value
negate (ZValue n) = ZValue (-n)
negate (ZxValue f x) = ZxValue (Zx.negate f) x
negate (GfpValue p a) = GfpValue p (Prime.negate p a)
negate (GfpxValue p f x) = GfpxValue p (Gfpx.negate p f) x

add :: Value -> Value -> Value
add v w = normalize $
    case align v w of
      (ZValue m, ZValue n) -> ZValue (m + n)
      (ZxValue f x, ZValue n) -> ZxValue (Zx.add f (Zx.constant n)) x
      (ZValue m, ZxValue g x) -> ZxValue (Zx.add (Zx.constant m) g) x
      (ZxValue f x, ZxValue g _) -> ZxValue (Zx.add f g) x
      (GfpValue p a, GfpValue _ b) -> GfpValue p (Prime.add p a b)
      (GfpxValue p f x, GfpValue _ b) -> GfpxValue p (Gfpx.add p f (Gfpx.constant b)) x
      (GfpValue p a, GfpxValue _ g x) -> GfpxValue p (Gfpx.add p (Gfpx.constant a) g) x
      (GfpxValue p f x, GfpxValue _ g _) -> GfpxValue p (Gfpx.add p f g) x
      _ -> error $ "cannot add values " ++ show v ++ " and " ++ show w

subtract :: Value -> Value -> Value
subtract v w = normalize $
    case align v w of
      (ZValue m, ZValue n) -> ZValue (m - n)
      (ZxValue f x, ZValue n) -> ZxValue (Zx.subtract f (Zx.constant n)) x
      (ZValue m, ZxValue g x) -> ZxValue (Zx.subtract (Zx.constant m) g) x
      (ZxValue f x, ZxValue g _) -> ZxValue (Zx.subtract f g) x
      (GfpValue p a, GfpValue _ b) -> GfpValue p (Prime.subtract p a b)
      (GfpxValue p f x, GfpValue _ b) -> GfpxValue p (Gfpx.subtract p f (Gfpx.constant b)) x
      (GfpValue p a, GfpxValue _ g x) -> GfpxValue p (Gfpx.subtract p (Gfpx.constant a) g) x
      (GfpxValue p f x, GfpxValue _ g _) -> GfpxValue p (Gfpx.subtract p f g) x
      _ -> error $ "cannot subtract values " ++ show v ++ " and " ++ show w

multiply :: Value -> Value -> Value
multiply v w = normalize $
    case align v w of
      (ZValue m, ZValue n) -> ZValue (m * n)
      (ZxValue f x, ZValue n) -> ZxValue (Zx.multiply f (Zx.constant n)) x
      (ZValue m, ZxValue g x) -> ZxValue (Zx.multiply (Zx.constant m) g) x
      (ZxValue f x, ZxValue g _) -> ZxValue (Zx.multiply f g) x
      (GfpValue p a, GfpValue _ b) -> GfpValue p (Prime.multiply p a b)
      (GfpxValue p f x, GfpValue _ b) -> GfpxValue p (Gfpx.multiply p f (Gfpx.constant b)) x
      (GfpValue p a, GfpxValue _ g x) -> GfpxValue p (Gfpx.multiply p (Gfpx.constant a) g) x
      (GfpxValue p f x, GfpxValue _ g _) -> GfpxValue p (Gfpx.multiply p f g) x
      _ -> error $ "cannot multiply values " ++ show v ++ " and " ++ show w

exp :: Value -> Value -> Value
exp (ZValue m) (ZValue n) = ZValue (m ^ n)
exp (ZxValue f x) (ZValue n) = normalize $ ZxValue (Zx.exp f n) x
exp (GfpValue p a) (ZValue n) = GfpValue p (Prime.exp p a n)
exp (GfpxValue p f x) (ZValue n) = normalize $ GfpxValue p (Gfpx.exp p f n) x
exp v w = error $ "cannot exponentiate values " ++ show v ++ " and " ++ show w

fromTerm :: Term -> Value
fromTerm = interpret emptyEnv ZContext

toTerm :: Value -> Term
toTerm (ZValue n) = IntegerTerm n
toTerm (ZxValue f x) = Zx.toTerm x f
toTerm (GfpValue p a) = Term.fromGfp p a
toTerm (GfpxValue p f x) = Gfpx.toTerm p x f

toString :: Value -> String
toString = Term.toString . toTerm

-------------------------------------------------------------------------------
-- Interpretation environments
-------------------------------------------------------------------------------

type Env = Map Var Value

emptyEnv :: Env
emptyEnv = Map.empty

lookupEnv :: Env -> Var -> Value
lookupEnv e x =
    case Map.lookup x e of
      Just v -> v
      Nothing -> ZxValue Zx.variable x

extendEnv :: Env -> Var -> Value -> Env
extendEnv e x v = Map.insert x v e

-------------------------------------------------------------------------------
-- Interpretation contexts
-------------------------------------------------------------------------------

data Context =
    ZContext
  | GfpContext Prime
  deriving (Eq,Ord,Show)

combineContext :: Context -> Context -> Context
combineContext ZContext c = c
combineContext (GfpContext p) (GfpContext q) | p /= q =
    error $ "cannot combine expressions (mod " ++ show p ++ ")" ++
            " and (mod " ++ show q ++ ")"
combineContext c _ = c

modContext :: Value -> Context
modContext (ZValue p) = GfpContext p
modContext v = error $ "cannot calculate modulo value " ++ show v

-------------------------------------------------------------------------------
-- Interpreting expressions
-------------------------------------------------------------------------------

context :: Value -> Context
context (ZValue _) = ZContext
context (ZxValue _ _) = ZContext
context (GfpValue p _) = GfpContext p
context (GfpxValue p _ _) = GfpContext p

reduceInContext :: Context -> Value -> Value
reduceInContext (GfpContext p) (ZValue n) =
    GfpValue p (Prime.fromInteger p n)
reduceInContext (GfpContext p) (ZxValue f x) =
    normalize (GfpxValue p (Gfpx.fromZx p f) x)
reduceInContext _ v = v

importIntoContext :: Context -> Value -> Value
importIntoContext c v = reduceInContext (combineContext c (context v)) v

align :: Value -> Value -> (Value,Value)
align v w =
    if Set.size xs <= 1 then (v',w')
    else error $ "more than one free variable in values " ++
                 show v' ++ " and " ++ show w'
  where
    xs = Set.union (free v') (free w')
    v' = reduceInContext c v
    w' = reduceInContext c w
    c = combineContext (context v) (context w)

interpret :: Env -> Context -> Term -> Value
interpret _ c (IntegerTerm n) = importIntoContext c (ZValue n)
interpret e c (NegateTerm t) = Factor.Value.negate (interpret e c t)
interpret e c (AddTerm t u) = add (interpret e c t) (interpret e c u)
interpret e c (SubtractTerm t u) = Factor.Value.subtract (interpret e c t) (interpret e c u)
interpret e c (MultiplyTerm t u) = multiply (interpret e c t) (interpret e c u)
interpret e c (ExpTerm t u) = Factor.Value.exp (interpret e c t) (interpret e ZContext u)
interpret e c (VarTerm x) = importIntoContext c (lookupEnv e x)
interpret e c (ModTerm t u) = interpret e c' t
  where c' = combineContext c (modContext (interpret e ZContext u))
interpret e c (LetTerm x t u) = interpret e' c u
  where e' = extendEnv e x (interpret e c t)
interpret _ _ tm = error $ "cannot interpret " ++ show tm
