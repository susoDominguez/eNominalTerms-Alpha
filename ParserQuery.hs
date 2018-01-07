module ParserQuery where

import qualified Data.Set as S
import Text.ParserCombinators.Parsec

import Alpha
import ParserTrm
import Query
import Rewriting
import Trm

-------------------------------------------------------------------------------
--parses a String with a given Parser; returns an error or the value of the parserp
inputL :: Parser a -> String -> Either PErr a
inputL p s = case parse p "" (whiteSpace >> s) of
                 Left e -> Left (show e)
                 Right x -> Right x


--parses a context and a list of constraints
{-parseAlphaQ :: Parser AlphaQ
parseAlphaQ = do fc <- parseCtx <|> return S.empty
                 spaces >>= string "|-"
                 prob <- parseProb
                 return (fc, prob)
-}
{-
parseCQ :: Parser CQ
parseCQ = do fc <- parseMFC "!"
             (try (do l <- parseTrm
                      string "->"
                      r <- parseTrm
                      eof
                      return (fc, [l, r]))
              <|> (do t <- parseTrm
                      eof
                      return (fc, [t])))

parseR :: Parser Rule
parseR = do r <- parseRule
            eof
            return r

parseT :: Parser TrmCtx
parseT = do fc <- try (do fc' <- parseCtx <|> return S.empty
                          String '|-'
                          return fc')
                  <|> return S.empty
            t <- parseTrm
            eof
            return (fc, t)

inputL :: Parser a -> String -> Either PErr a
inputL p s = case parse p "" (strip s) of
                 Left e -> Left (show e)
                 Right x -> Right x

-------------------------------------------------------------------------------

pAQ :: String -> String -> Either PErr AQ
pAQ s1 s2
    = case (inputL parseEqu s1, inputL parseAQ s2) of
          (Left e, _) -> Left e
          (_, Left e) -> Left e
          (Right eq, Right (fc, cp)) -> Right (eq, fc, cp)

pCQ :: String -> Either PErr CQ
pCQ = inputL parseCQ

pRQ :: [String] -> String -> Either PErr RQ
pRQ s1 s2
    = case (rs, t) of
          (Left e, _) -> Left e
          (_, Left e) -> Left e
          (Right rs', Right (fc, t')) -> Right (rs', fc, t')
    where rs = sequence (map (inputL parseR) s1)
          t = inputL parseT s2
