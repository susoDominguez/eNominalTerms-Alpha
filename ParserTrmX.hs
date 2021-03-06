module ParserTrmX where

import Text.ParserCombinators.Parsec
import qualified Data.Char as R
import qualified Data.Set as S
import qualified Data.Map as M
import TrmX
import ConstraintsX
-------------------------------------------------
{-trms grammar-}

type PErr = String

--atoms: string starting w lower case letter
parseAtm :: Parser Atm
parseAtm = do
  x <- lower
  r <- many  digit --so no a' or aa but a, a0, a00
  return (x:r) <?> "Atom"
 -- r <- many (lower <|> digit)


--variables: string starting w upper case letter
parseVar :: Parser Var
parseVar = do
  x <- upper
  r <- many digit 
  return (x:r) <?> "Variable"

--function name: string starting with '
parseFun :: Parser Fun 
parseFun = do
  x <- char '\''
  r <- many1 alphaNum
  return (x:r)  <?> "Function symbol"

--swapping : 2 atoms separated by a space in between brackets
parseTrans:: Parser (Atm,Atm)
parseTrans = between (char '(') (char ')') p  <?> "Swapping"
            where p = do
                    a <- parseAtm
                    space
                    b <- parseAtm
                    return (a,b)

--permutation : must be reversed
parsePrm :: Parser Prm
parsePrm = fmap reverse (many1 parseTrans) <?> "Permutation"

--a-substitution: atom and term separated by arrow, between [] and 1 space in between
parseAsb:: Parser (Atm,Trm)
parseAsb = between (char '[') (char ']') p
            where p = do
                    a <-  parseAtm
                    spaces >> string "->"
                    t <- spaces >> parseTrm
                    return (a,t) <?> "Atom to Term Substitution"

--many a-substitutions, must be reversed
parseAsbs :: Parser Asb
parseAsbs = fmap M.fromList (many1 parseAsb) <?> "Atom to Term substitution list"

--parse freshness context
parseCtx :: Parser Ctx
parseCtx =
  fmap S.fromList (between (char '{') (char '}') (sepBy p (char ','))) <?> "freshness context"
    where p = do a <- (spaces >> parseAtm)
                 char '#'
                 x <- parseVar
                 return (a, x)


--parse an extended nominal term
parseTrm:: Parser Trm
parseTrm = try parseAbsTrm <|> try parseVarTrm1 <|> parseAppTrm <|> parseVarTrm  <|> parseAtmTrm <|>  try parseVarTrm2    <|>  parseTplTrm   <?> "Nominal Term"

parseAppTrm, parseAtmTrm, parseAbsTrm, parseVarTrm, parseVarTrm1, parseVarTrm2, parseTplTrm ::Parser Trm
parseAppTrm = do
              f <- parseFun
              t <- do
                spaces
                try parseTrm <|>
                   try (eof >> return (TplTrm [])) <|>
                      (lookAhead (oneOf ",])=") >> return (TplTrm []))
              return (AppTrm f t)  
parseAtmTrm =  fmap AtmTrm parseAtm
parseAbsTrm = do
              char '['
              a <-  parseAtm
              char ']'
              t <- spaces >> parseTrm
              return (AbsTrm a t)
parseVarTrm = do
              x <-  parseVar
              return (VarTrm M.empty [] x)
parseVarTrm1 = do
               sb <- parseAsbs
               pr <- try (char '^' >> parsePrm) <|> (return []) 
               x <- char '+' >> parseVar
               return (VarTrm sb pr x)
parseVarTrm2 = do
               pr <-  parsePrm
               x <- char '+' >> parseVar
               return (VarTrm M.empty pr x)
parseTplTrm = fmap TplTrm (between (char '(') (char ')')( p `sepBy1`  (char ',')))
   where p = do  t <- spaces >> parseTrm
                 return t

parseTrmCtx:: Parser TrmCtx
parseTrmCtx = do
              ctx <- try (parseCtx) <|> (return S.empty)
              space
              string "|-"
              space
              t <- parseTrm
              return (ctx, t)

parseConstr :: Parser (ConstrX Trm)
parseConstr = try eq <|> frsh
      where frsh = do a <- spaces >> parseAtm
                      char '#'
                      t <- parseTrm
                      return (F (AtmTrm a) t)
            eq = do t1 <- spaces >>  parseTrm
                    spaces
                    char '='
                    t2 <- spaces >> parseTrm
                    spaces
                    return (Eq t1 t2) <?> "#|= Constrain"

parseProb :: Parser Prob
parseProb = do xs <- sepBy parseConstr (char ',')
               spaces >> eof
               return xs <?> "List of #|= Constrains"



--parses a String with a given Parser; returns an error or the value of the parserp
runParserX :: Parser a -> String -> Either PErr a
runParserX p s = case (parse p "" s) of
                    Left e -> Left (show e)
                              Right x -> Right x 
