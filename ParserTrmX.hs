module ParserTrm where

import Text.ParserCombinators.Parsec
import qualified Data.Char as R
import qualified Data.Set as S
import TrmX

-------------------------------------------------
{-trms grammar-}

--atoms: string starting w lower case letter
parseAtm :: Parser Atm
parseAtm = do
  x <- lower
  r <- many (lower <|> char '\'' <|> digit)
  return (x:r) <?> "Atom"

--variables: string starting w upper case letter
parseVar :: Parser Var
parseVar = do
  x <- upper
  r <- many (upper <|> char '\'' <|> digit)
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
parsePrm = fmap reverse (many1 parseSwap) <?> "permutation"

--a-substitution: atom and term separated by arrow,between [] and reversed
parse1Asub:: Parser (Atm,TrmX)
parse1Asub = between (char '[') (char ']') p
            where p = do
                    a <- spaces >> parseAtm
                    spaces
                    string "->"
                    t <- spaces >> parseTrm
                    spaces
                    return (a,t) <?> "Atom to Term Substitution"

--many a-substitutions
parseAsub:: Parser Asub
parseAsub = fmap reverse (many1 parse1Asub) <?> "Atom to Term substitution list"

--parse freshness context
parseCtx :: Parser Ctx
parseCtx = fmap S.fromList (between (char '{' >> spaces) (spaces >> char '}') (sepBy p (char ','))) <?> "freshness context"
    where p = do a <- (spaces >> parseAtm)
                 char '#'
                 x <- parseVar
                 spaces
                 return (a, x)

--parse an extended nominal term
parseTrm:: Parser TrmX
parseTrm = try parseAbsTrm <|> try parseVarTrm1 <|> parseAppTrm <|> parseVarTrm  <|> parseAtmTrm <|>  try parseVarTrm2    <|>  parseTplTrm   <?> "Nominal Term"

parseAppTrm, parseAtmTrm, parseAbsTrm, parseVarTrm, parseVarTrm1, parseVarTrm2, parseTplTrm ::Parser TrmX
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
              a <- spaces >> parseAtm
              spaces 
              char ']'
              t <- spaces >> parseTrm
              return (AbsTrm a t)
parseVarTrm = do
              x <-  parseVar
              return (VarTrm [] [] x)
parseVarTrm1 = do
               sb <- parseAsub
               pr <- try (char '^' >> parsePrm) <|> (return []) 
               x <- char '+' >> parseVar
               return (VarTrm sb pr x)
parseVarTrm2 = do
               pr <-  parsePrm
               x <- char '+' >> parseVar
               return (VarTrm []  pr x)
parseTplTrm = fmap TplTrm (between (char '(') (char ')')( p `sepBy1`  (char ',')))
   where p = do  t <- spaces >> parseTrm
                 spaces
                 return t

parseTrmCtx:: Parser TrmCtx
parseTrmCtx = do
              ctx <- try (parseCtx) <|> (return S.empty)
              spaces
              string "|-"
              spaces
              t <- parseTrm
              return (ctx, t)

parseConstr :: Parser ConstrX
parseConstr = try eq <|> frsh
      where eq = do a <- spaces >> parseAtm
                    char '#'
                    t <- parseTrm
                    spaces
                    return (F a t)
            frsh = do t1 <- spaces >>  parseTrm
                      spaces
                      char '='
                      t2 <- spaces >> parseTrm
                      spaces
                      return (E t1 t2) <?> "#|= Constrain"

parseProb :: Parser Prob
parseProb = do xs <- sepBy parseConstr (char ',')
               spaces >> eof
               return xs <?> "List of #|= Constrains"
