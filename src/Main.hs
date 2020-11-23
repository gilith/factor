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

import Data.Char (isSpace)
import Data.List (dropWhileEnd)
import Data.Version (showVersion)
import Paths_factor (version)
import System.Console.GetOpt
import System.Environment (getArgs,getProgName)
import System.Exit (ExitCode(..),exitWith)
import System.IO (hPutStr,hPutStrLn,stderr)
import qualified System.Random as Random

import qualified Factor
import qualified Factor.Nfs as Nfs
import Factor.Term (Term)
import qualified Factor.Term as Term
import Factor.Util
import qualified Factor.Value as Value

-------------------------------------------------------------------------------
-- Options
-------------------------------------------------------------------------------

data Options =
    Options
      {trialOptions :: Integer,
       nfsVerboseOptions :: Bool,
       verboseOptions :: Bool}

defaultOptions :: Options
defaultOptions =
    Options
      {trialOptions = Factor.trialDivisionConfig Factor.defaultConfig,
       nfsVerboseOptions = False,
       verboseOptions = False}

options :: [ OptDescr (Options -> IO Options) ]
options =
    [Option "" ["trial"]
       (ReqArg
          (\arg opt -> return opt {trialOptions = read arg})
          "N")
       "Set trial division maximum to N",

     Option "v" ["verbose"]
       (NoArg
          (\opt -> return opt {verboseOptions = True}))
       "Enable verbose messages",

     Option "" ["nfs-verbose"]
       (NoArg
          (\opt -> return opt {nfsVerboseOptions = True}))
       "Show complete lists in NFS verbose messages",

     Option "" ["version"]
       (NoArg
          (\_ -> do
             prg <- getProgName
             hPutStrLn stderr (prg ++ " version " ++ showVersion version)
             exitWith ExitSuccess))
       "Print version",

     Option "h" ["help"]
       (NoArg
          (\_ -> printUsage))
       "Show help"]

examples :: String
examples =
   "Example input expressions:\n" ++
   fmtTable (Table False True 2)
     [["  2047","Concrete integer"],
      ["  2^2^7 + 1","Integer expression"],
      ["  N[100]","Random 100-bit positive integer"],
      ["  P[50] * P[50]","Product of random 50-bit primes"],
      ["  x^4 - 10*x^2 + 1","Polynomial over the integers"],
      ["  x^5^2 - x (mod 5)","Polynomial over GF(5)"]] ++
   "Let expressions are supported: let p = P[4] in x^p - x (mod p)\n" ++
   "Multivariate polynomials (e.g., y^2 - x^3 - a*x - b) are not supported"

printUsage :: IO a
printUsage = do
    prg <- getProgName
    usage <- pure $ "Usage: " ++ prg ++ " [options] \"expression to factor\""
    hPutStr stderr (usageInfo usage options)
    hPutStrLn stderr examples
    exitWith ExitSuccess

processCommandLine :: [String] -> IO (Options,String)
processCommandLine [] = printUsage
processCommandLine args = do
    (io,nopts,err) <- pure $ getOpt RequireOrder options args
    (if null err then pure () else error (dropWhileEnd isSpace $ unlines err))
    opts <- foldl (>>=) (return defaultOptions) io
    expr <- case nopts of
              [] -> error "no input expression"
              [w] -> pure w
              _ : _ : _ -> error "multiple input expressions"
    pure (opts,expr)

factorConfig :: Options -> Factor.Config
factorConfig opts = cfg
    {Factor.trialDivisionConfig = trialOptions opts,
     Factor.nfsConfig = nfs
       {Nfs.verboseConfig = nfsVerboseOptions opts}}
  where
    cfg = Factor.defaultConfig
    nfs = Factor.nfsConfig cfg

-------------------------------------------------------------------------------
-- Main program
-------------------------------------------------------------------------------

outputTerm :: Term -> IO ()
outputTerm = putStrLn . Term.toString

outputTermChange :: String -> Term -> IO ()
outputTermChange s tm = do { putStrLn s ; outputTerm tm }

outputTermIfChanged :: Term -> String -> Term -> IO ()
outputTermIfChanged tm _ tm' | tm' == tm = return ()
outputTermIfChanged _ s tm' = outputTermChange s tm'

main :: IO ()
main = do
    -- Process command line
    args <- getArgs
    (opts,expr) <- processCommandLine args
    Options {verboseOptions = verbose} <- pure opts
    -- Parse the input expression as a term
    tm <- pure $ case Term.parse expr of
                   Left e -> error $ show e
                   Right t -> t
    outputTerm tm
    -- Pick random subterms
    rnd <- Random.getStdGen
    (tm',rnd') <- pure $ Term.uniform tm rnd
    outputTermIfChanged tm "-->" tm'
    -- Interpret the term as a value
    val <- pure $ Value.fromTerm tm'
    tm'' <- pure $ Value.toTerm val
    outputTermIfChanged tm' "==" tm''
    -- Factor the value
    cfg <- pure $ factorConfig opts
    (fac,_) <- (if verbose then runVerbose else pure . runQuiet)
               (Factor.factorValue cfg val rnd')
    outputTermChange "==" fac
    return ()
