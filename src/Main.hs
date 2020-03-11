{- |
module: Main
description: Factoring positive integers
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Main
  ( main )
where

import qualified Arithmetic.Random
import Arithmetic.Prime.Factor (Factor)
import qualified Arithmetic.Prime.Factor as Factor
--import qualified Arithmetic.Modular as Modular
--import qualified Arithmetic.Montgomery as Montgomery
import qualified Arithmetic.Williams as Williams
--import qualified Data.List as List
import qualified System.Environment as Environment
import qualified System.Random
import OpenTheory.Primitive.Natural
import OpenTheory.Primitive.Random (Random)
import qualified OpenTheory.Primitive.Random
--import qualified OpenTheory.Natural.Uniform as Uniform

--------------------------------------------------------------------------------
-- Natural number inputs
--------------------------------------------------------------------------------

data InputNatural =
    Fixed Natural
  | Width Natural
  deriving Show

stringToInputNatural :: String -> InputNatural
stringToInputNatural s =
    case s of
      '[' : s' -> case reads s' of
                    [(w,"]")] -> Width w
                    _ -> usage "bad N argument"
      _ -> case reads s of
            [(n,"")] -> Fixed n
            _ -> usage "bad N argument"

widthInputNatural :: InputNatural -> Random -> Natural
widthInputNatural (Fixed n) _ = n
widthInputNatural (Width w) r = Arithmetic.Random.randomWidth w r

oddInputNatural :: InputNatural -> Random -> Natural
oddInputNatural (Fixed n) _ = n
oddInputNatural (Width w) r = Arithmetic.Random.randomOdd w r

rsaInputNatural :: InputNatural -> Random -> Natural
rsaInputNatural (Fixed n) _ = n
rsaInputNatural (Width w) rnd = Factor.toNatural (Factor.randomRSA w rnd)

--------------------------------------------------------------------------------
-- Options
--------------------------------------------------------------------------------

usage :: String -> a
usage err =
    error $ err ++ "\n" ++ info
  where
    info = "Usage: factor N\nwhere N is a positive integer"

processArguments :: [String] -> InputNatural
processArguments [] = usage "missing N argument"
processArguments [s] = stringToInputNatural s
processArguments (_ : _ : _) = usage "too many arguments"

--------------------------------------------------------------------------------
-- Computation
--------------------------------------------------------------------------------

factorWilliams :: Natural -> Random -> Maybe Factor
factorWilliams = Factor.factor 1000 (Williams.factor 5 Nothing)

factor :: InputNatural -> Random -> String
factor i rnd =
    case factorWilliams n r2 of
      Nothing -> error $ "factorization failed for " ++ show n
      Just f -> show n ++ (if Factor.isPrime f then " is prime"
                           else " == " ++ show f)
  where
    n = widthInputNatural i r1
    (r1,r2) = OpenTheory.Primitive.Random.split rnd

--------------------------------------------------------------------------------
-- Main program
--------------------------------------------------------------------------------

main :: IO ()
main =
    do args <- Environment.getArgs
       rnd <- fmap OpenTheory.Primitive.Random.fromInt System.Random.randomIO
       let n = processArguments args
       putStrLn $ factor n rnd
       return ()
