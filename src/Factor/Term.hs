{- |
module: Factor.Term
description: Expression terms
license: MIT

maintainer: Joe Leslie-Hurd <joe@gilith.com>
stability: provisional
portability: portable
-}
module Factor.Term
where

--import Control.Monad (filterM)
import qualified Data.Char as Char
import qualified Data.List as List
--import qualified Data.Maybe as Maybe
import System.Random (RandomGen)
--import qualified System.Random as Random
import Text.Parsec ((<|>),Parsec,ParseError)
import qualified Text.Parsec as Parsec
--import Text.Parsec.Text.Lazy ()
import Text.PrettyPrint ((<>),(<+>),Doc)
import qualified Text.PrettyPrint as PP

--import Factor.Gfpx (Gfpx)
--import qualified Factor.Gfpx as Gfpx
import Factor.Prime (Gfp,Prime,PrimePower)
import qualified Factor.Prime as Prime
import Factor.Util
--import Factor.Zx ()
--import qualified Factor.Zx as Zx

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

type Var = String

data Term =
    IntegerTerm Integer
  | NumberTerm Width
  | PrimeTerm Width
  | CompositeTerm Width
  | NegateTerm Term
  | AddTerm Term Term
  | SubtractTerm Term Term
  | MultiplyTerm Term Term
  | ExpTerm Term Term
  | VarTerm Var
  | ModTerm Term Term
  | LetTerm Var Term Term
  deriving (Eq,Ord,Show)

-------------------------------------------------------------------------------
-- Constructors and destructors
-------------------------------------------------------------------------------

modulo :: Term -> Integer -> Term
modulo t p = ModTerm t (IntegerTerm p)

fromGfp :: Prime -> Gfp -> Term
fromGfp p x = modulo (IntegerTerm (Prime.toSmallestInteger p x)) p

fromPrimePower :: PrimePower -> Term
fromPrimePower (p,1) = IntegerTerm p
fromPrimePower (p,k) = ExpTerm (IntegerTerm p) (IntegerTerm k)

fromPrimePowers :: [PrimePower] -> Term
fromPrimePowers = mkProduct . map fromPrimePower

mkSum :: [Term] -> Term
mkSum [] = IntegerTerm 0
mkSum (t1 : ts) = List.foldl' (\t u -> AddTerm t u) t1 ts

mkProduct :: [Term] -> Term
mkProduct [] = IntegerTerm 1
mkProduct (t1 : ts) = List.foldl' (\t u -> MultiplyTerm t u) t1 ts

-------------------------------------------------------------------------------
-- Subterms (used for shrinking QuickCheck counterexamples)
-------------------------------------------------------------------------------

subterms :: Term -> [Term]
subterms (NegateTerm t) = [t]
subterms (AddTerm t u) = [t,u]
subterms (SubtractTerm t u) = [t,u]
subterms (MultiplyTerm t u) = [t,u]
subterms (ExpTerm t u) = [t,u]
subterms (ModTerm t u) = [t,u]
subterms (LetTerm _ e t) = [e,t]
subterms _ = []

-------------------------------------------------------------------------------
-- Rewriting terms
-------------------------------------------------------------------------------

data Result =
    RewriteResult Term
  | UnchangedResult
  | ErrorResult
  deriving (Eq,Ord,Show)

newtype Rewrite = Rewrite { unRewrite :: Term -> Result }

applyRewrite :: Rewrite -> Term -> Maybe Term
applyRewrite rw tm =
    case unRewrite rw tm of
      RewriteResult tm' -> Just tm'
      UnchangedResult -> Just tm
      ErrorResult -> Nothing

applyRewriteUnsafe :: Rewrite -> Term -> Term
applyRewriteUnsafe rw tm =
    case applyRewrite rw tm of
      Just tm' -> tm'
      Nothing -> error $ "couldn't rewrite " ++ show tm

idRewrite :: Rewrite
idRewrite = Rewrite (const UnchangedResult)

errorRewrite :: Rewrite
errorRewrite = Rewrite (const ErrorResult)

tryRewrite :: Rewrite -> Rewrite
tryRewrite (Rewrite rw) = Rewrite $ \tm ->
    case rw tm of
      ErrorResult -> UnchangedResult
      res -> res

thenRewrite :: Rewrite -> Rewrite -> Rewrite
thenRewrite (Rewrite rw1) (Rewrite rw2) = Rewrite $ \tm ->
    case rw1 tm of
      res1 @ (RewriteResult tm') ->
        case rw2 tm' of
          UnchangedResult -> res1
          res2 -> res2
      UnchangedResult -> rw2 tm
      ErrorResult -> ErrorResult

orelseRewrite :: Rewrite -> Rewrite -> Rewrite
orelseRewrite (Rewrite rw1) (Rewrite rw2) = Rewrite $ \tm ->
    case rw1 tm of
      ErrorResult -> rw2 tm
      res1 -> res1

firstRewrite :: [Rewrite] -> Rewrite
firstRewrite = foldr orelseRewrite errorRewrite

subtermRewrite :: Rewrite -> Rewrite
subtermRewrite (Rewrite rw) = Rewrite sub
  where
    sub (NegateTerm t) = sub1 NegateTerm t
    sub (AddTerm t u) = sub2 AddTerm t u
    sub (SubtractTerm t u) = sub2 SubtractTerm t u
    sub (MultiplyTerm t u) = sub2 MultiplyTerm t u
    sub (ExpTerm t u) = sub2 ExpTerm t u
    sub (ModTerm t u) = sub2 ModTerm t u
    sub (LetTerm v e t) = sub2 (LetTerm v) e t
    sub _ = UnchangedResult

    sub1 c t =
        case rw t of
          RewriteResult t' -> RewriteResult $ c t'
          UnchangedResult -> UnchangedResult
          ErrorResult -> ErrorResult

    sub2 c t u =
        case (rw t, rw u) of
          (RewriteResult t', RewriteResult u') -> RewriteResult $ c t' u'
          (RewriteResult t', UnchangedResult) -> RewriteResult $ c t' u
          (UnchangedResult, RewriteResult u') -> RewriteResult $ c t u'
          (UnchangedResult, UnchangedResult) -> UnchangedResult
          _ -> ErrorResult

-- Never returns an error result
bottomUpRewrite :: Rewrite -> Rewrite
bottomUpRewrite rw = go
  where go = thenRewrite (subtermRewrite go) (tryRewrite rw)

-------------------------------------------------------------------------------
-- Expanding let terms
-------------------------------------------------------------------------------

instVarRewrite :: Var -> Term -> Rewrite
instVarRewrite v t = Rewrite inst
  where
    inst (VarTerm w) | w == v = res
    inst _ = ErrorResult

    res = if t == VarTerm v then UnchangedResult else RewriteResult t

expandLetRewrite :: Rewrite -> (Rewrite -> Rewrite) -> Rewrite
expandLetRewrite (Rewrite rw1) rw2 = Rewrite bind
  where
    bind (LetTerm v e t) =
        case rw1 e of
          RewriteResult e' -> body (rw2 $ instVarRewrite v e') t
          UnchangedResult -> body (rw2 $ instVarRewrite v e) t
          ErrorResult -> ErrorResult
    bind _ = ErrorResult

    body (Rewrite rw) t =
        case rw t of
          UnchangedResult -> RewriteResult t
          res -> res

-- Never returns an error result
expandLetsRewrite :: Rewrite -> Rewrite
expandLetsRewrite = go
  where
    go rw = orelseRewrite
              (expandLetRewrite (go rw) (go . flip orelseRewrite rw))
              (thenRewrite (subtermRewrite (go rw)) (tryRewrite rw))

-------------------------------------------------------------------------------
-- Picking random numbers
-------------------------------------------------------------------------------

uniform :: RandomGen r => Term -> r -> (Term,r)
uniform (NumberTerm w) r = (IntegerTerm n, r')
  where (n,r') = uniformInteger w r
uniform (PrimeTerm w) r = (IntegerTerm p, r')
  where (p,r') = Prime.uniformPrime w r
uniform (CompositeTerm w) r = (IntegerTerm c, r')
  where (c,r') = Prime.uniformComposite w r
uniform (NegateTerm t) r = (NegateTerm t', r')
  where (t',r') = uniform t r
uniform (AddTerm t u) r = (AddTerm t' u', r'')
  where
    (t',r') = uniform t r
    (u',r'') = uniform u r'
uniform (SubtractTerm t u) r = (SubtractTerm t' u', r'')
  where
    (t',r') = uniform t r
    (u',r'') = uniform u r'
uniform (MultiplyTerm t u) r = (MultiplyTerm t' u', r'')
  where
    (t',r') = uniform t r
    (u',r'') = uniform u r'
uniform (ExpTerm t u) r = (ExpTerm t' u', r'')
  where
    (t',r') = uniform t r
    (u',r'') = uniform u r'
uniform (ModTerm t u) r = (ModTerm t' u', r'')
  where
    (t',r') = uniform t r
    (u',r'') = uniform u r'
uniform (LetTerm v e t) r = (LetTerm v e' t', r'')
  where
    (e',r') = uniform e r
    (t',r'') = uniform t r'
uniform tm r = (tm,r)

-------------------------------------------------------------------------------
-- Lifting negations
-------------------------------------------------------------------------------

negativeIntegerRewrite :: Rewrite
negativeIntegerRewrite = Rewrite rw
  where
    rw (IntegerTerm i) | i < 0 = RewriteResult $ NegateTerm (IntegerTerm (-i))
    rw _ = ErrorResult

negateNegateRewrite :: Rewrite
negateNegateRewrite = Rewrite rw
  where
    rw (NegateTerm (NegateTerm t)) = RewriteResult t
    rw _ = ErrorResult

addNegate2Rewrite :: Rewrite
addNegate2Rewrite = Rewrite rw
  where
    rw (AddTerm t (NegateTerm u)) = RewriteResult $ SubtractTerm t u
    rw _ = ErrorResult

subtractNegate2Rewrite :: Rewrite
subtractNegate2Rewrite = Rewrite rw
  where
    rw (SubtractTerm t (NegateTerm u)) = RewriteResult $ AddTerm t u
    rw _ = ErrorResult

multiplyNegateRewrite :: Rewrite
multiplyNegateRewrite = Rewrite rw
  where
    rw (MultiplyTerm (NegateTerm t) (NegateTerm u)) = RewriteResult $ MultiplyTerm t u
    rw (MultiplyTerm t (NegateTerm u)) = RewriteResult $ NegateTerm (MultiplyTerm t u)
    rw (MultiplyTerm (NegateTerm t) u) = RewriteResult $ NegateTerm (MultiplyTerm t u)
    rw _ = ErrorResult

nnfInteger :: Term -> Term
nnfInteger = applyRewriteUnsafe (bottomUpRewrite negativeIntegerRewrite)

nnf :: Term -> Term
nnf = applyRewriteUnsafe $ bottomUpRewrite $ firstRewrite
        [negativeIntegerRewrite,
         negateNegateRewrite,
         addNegate2Rewrite,
         subtractNegate2Rewrite,
         multiplyNegateRewrite]

-------------------------------------------------------------------------------
-- Simplifying terms
-------------------------------------------------------------------------------

multiplyOneRewrite :: Rewrite
multiplyOneRewrite = Rewrite rw
  where
    rw (MultiplyTerm (IntegerTerm 1) u) = RewriteResult u
    rw (MultiplyTerm t (IntegerTerm 1)) = RewriteResult t
    rw _ = ErrorResult

expOneRewrite :: Rewrite
expOneRewrite = Rewrite rw
  where
    rw (ExpTerm (IntegerTerm 1) _) = RewriteResult $ IntegerTerm 1
    rw (ExpTerm t (IntegerTerm 1)) = RewriteResult t
    rw _ = ErrorResult

expZeroRewrite :: Rewrite
expZeroRewrite = Rewrite rw
  where
    rw (ExpTerm _ (IntegerTerm 0)) = RewriteResult $ IntegerTerm 1
    rw _ = ErrorResult

simplify :: Term -> Term
simplify = applyRewriteUnsafe $ bottomUpRewrite $ firstRewrite
        [multiplyOneRewrite,
         expOneRewrite,
         expZeroRewrite]

-------------------------------------------------------------------------------
-- Parsing terms
-------------------------------------------------------------------------------

isReservedWord :: String -> Bool
isReservedWord "in" = True
isReservedWord "let" = True
isReservedWord "mod" = True
isReservedWord _ = False

spaceParser :: Parsec String st ()
spaceParser = Parsec.oneOf " \t\n" >> return ()

spacesParser :: Parsec String st ()
spacesParser = Parsec.skipMany spaceParser

spaces1Parser :: Parsec String st ()
spaces1Parser = Parsec.skipMany1 spaceParser

integerParser :: Parsec String st Integer
integerParser = zero <|> positive
  where
    zero = do
        _ <- Parsec.char '0'
        return 0

    positive = do
        h <- positiveDigit
        t <- Parsec.many digit
        return (List.foldl' (\n d -> 10*n + d) h t)

    digit = zero <|> positiveDigit

    positiveDigit = do
        d <- Parsec.oneOf "123456789"
        return (toInteger $ Char.digitToInt d)

widthParser :: Parsec String st Width
widthParser = do
    _ <- Parsec.char '['
    spacesParser
    i <- integerParser
    spacesParser
    _ <- Parsec.char ']'
    return $ fromInteger i

classWidthParser :: Char -> Parsec String st Width
classWidthParser c = do
    _ <- Parsec.char c
    spacesParser
    widthParser

numberParser :: Parsec String st Width
numberParser = classWidthParser 'N'

primeParser :: Parsec String st Width
primeParser = classWidthParser 'P'

compositeParser :: Parsec String st Width
compositeParser = classWidthParser 'C'

varParser :: Parsec String st Var
varParser = Parsec.try $ do
    c <- Parsec.lower
    cs <- Parsec.many Parsec.alphaNum
    let v = c : cs
    if isReservedWord v then Parsec.parserFail "reserved word" else return v

termParser :: Parsec String st Term
termParser = do { spacesParser ; t <- topTm ; spacesParser ; return t }
  where
    parensTm = Parsec.try $ do
        _ <- Parsec.char '('
        spacesParser
        t <- topTm
        spacesParser
        _ <- Parsec.char ')'
        return t

    topTm = letTm <|> modTm

    letTm = do
        _ <- Parsec.string "let"
        spaces1Parser
        v <- varParser
        spacesParser
        _ <- Parsec.char '='
        spacesParser
        e <- sumTm
        spacesParser
        _ <- Parsec.string "in"
        spaces1Parser
        t <- modTm
        return $ LetTerm v e t

    modTm = do
        t <- sumTm
        spacesParser
        m <- Parsec.optionMaybe modOpTm
        return $ case m of { Nothing -> t ; Just p -> ModTerm t p }

    modOpTm = Parsec.try $ do
        _ <- Parsec.char '('
        spacesParser
        _ <- Parsec.string "mod"
        spaces1Parser
        t <- expTm
        spacesParser
        _ <- Parsec.char ')'
        return t

    sumTm = do
        t1 <- negTm <|> prodTm
        spacesParser
        ts <- Parsec.many addTm
        return $ List.foldl' (\t (c,u) -> c t u) t1 ts

    addTm = do
        o <- addOp
        spacesParser
        t <- prodTm
        return (o,t)

    addOp =
        (Parsec.char '+' >> return AddTerm) <|>
        (Parsec.char '-' >> return SubtractTerm)

    negTm = do
        _ <- Parsec.char '-'
        spacesParser
        t <- prodTm
        return $ NegateTerm t

    prodTm = do
        t1 <- expTm
        spacesParser
        ts <- Parsec.many multTm
        return $ mkProduct (t1 : ts)

    multTm = do
        _ <- Parsec.char '*'
        spacesParser
        expTm

    expTm = do
        t <- atomicTm
        spacesParser
        m <- Parsec.optionMaybe expOpTm
        return $ case m of { Nothing -> t ; Just e -> ExpTerm t e }

    expOpTm = do
        _ <- Parsec.char '^'
        spacesParser
        expTm

    atomicTm =
        (IntegerTerm <$> integerParser) <|>
        (NumberTerm <$> numberParser) <|>
        (PrimeTerm <$> primeParser) <|>
        (CompositeTerm <$> compositeParser) <|>
        (PrimeTerm <$> primeParser) <|>
        (VarTerm <$> varParser) <|>
        parensTm

parse :: String -> Either ParseError Term
parse = Parsec.parse (termParser <* Parsec.eof) ""

fromString :: String -> Maybe Term
fromString s = case parse s of { Left _ -> Nothing ;  Right t -> Just t }

-------------------------------------------------------------------------------
-- Pretty-printing terms
-------------------------------------------------------------------------------

widthToDoc :: Width -> Doc
widthToDoc = PP.brackets . PP.int

atomicToDoc :: Term -> Doc
atomicToDoc (IntegerTerm n) = PP.integer n
atomicToDoc (NumberTerm w) = PP.char 'N' <> widthToDoc w
atomicToDoc (PrimeTerm w) = PP.char 'P' <> widthToDoc w
atomicToDoc (CompositeTerm w) = PP.char 'C' <> widthToDoc w
atomicToDoc (VarTerm v) = PP.text v
atomicToDoc tm = PP.parens (toDoc tm)

expToDoc :: Term -> Doc
expToDoc = PP.fcat . strip
  where
    strip (ExpTerm t u) = (atomicToDoc t <> PP.char '^') : strip u
    strip t = [atomicToDoc t]

prodToDoc :: Term -> Doc
prodToDoc = strip []
  where
    strip l (MultiplyTerm t u) = strip ((PP.char '*' <+> expToDoc u) : l) t
    strip l t = PP.fsep (expToDoc t : l)

negateToDoc :: Term -> Doc
negateToDoc (NegateTerm t) = PP.char '-' <> prodToDoc t
negateToDoc tm = prodToDoc tm

sumToDoc :: Term -> Doc
sumToDoc = strip []
  where
    strip l (AddTerm t u) = strip ((PP.char '+' <+> prodToDoc u) : l) t
    strip l (SubtractTerm t u) = strip ((PP.char '-' <+> prodToDoc u) : l) t
    strip l t = PP.fsep (negateToDoc t : l)

modToDoc :: Term -> Doc
modToDoc (ModTerm t m) =
    sumToDoc t <+> PP.parens (PP.text "mod" <+> expToDoc m)
modToDoc tm = sumToDoc tm

toDoc :: Term -> Doc
toDoc (LetTerm v e t) =
    PP.text "let" <+> PP.text v <+> PP.char '=' <+>
    sumToDoc e <+> PP.text "in" <+> modToDoc t
toDoc tm = modToDoc tm

toString :: Term -> String
toString = PP.renderStyle style . toDoc
  where style = PP.style {PP.lineLength = 80, PP.ribbonsPerLine = 1.0}

{-
let tm = ModTerm (NegateTerm (PrimeTerm 3)) (CompositeTerm 1)
let tm = AddTerm (IntegerTerm 1) (CompositeTerm 1)
let tm = ModTerm (NumberTerm 2) (NumberTerm 1)
let tm = ModTerm (IntegerTerm 2) (IntegerTerm 1)
let tm = AddTerm (CompositeTerm 1) (PrimeTerm 1)
let tm = ModTerm (ExpTerm (IntegerTerm 3) (PrimeTerm 5)) (ExpTerm (NumberTerm 4) (NumberTerm 1))
let tm = ExpTerm (ExpTerm VarTerm (NegateTerm (MultiplyTerm VarTerm (PrimeTerm 6)))) (AddTerm (ModTerm (PrimeTerm 27) (ExpTerm (PrimeTerm 29) (NumberTerm 10))) (ExpTerm (MultiplyTerm (MultiplyTerm (SubtractTerm (IntegerTerm 17) VarTerm) (AddTerm (IntegerTerm 26) (IntegerTerm 5))) (ModTerm VarTerm (MultiplyTerm (NumberTerm 36) VarTerm))) (AddTerm VarTerm (CompositeTerm 3))))
let tm = MultiplyTerm (ExpTerm (NumberTerm 17) (IntegerTerm 10)) (IntegerTerm 3)
let tm = nnfInteger $ LetTerm "x" (ExpTerm (IntegerTerm (-2)) (NumberTerm 0)) (AddTerm (CompositeTerm 2) (IntegerTerm 2))
let s = toString tm
putStrLn s
fromString s
Parsec.parse parser "" s
-}
