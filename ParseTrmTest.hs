module ParserTrmTest where

import Test.Hspec
import TrmX
import ConstraintsX
import Text.ParserCombinators.Parsec
import qualified Data.Map as M
import qualified Data.Set as S
import ParserTrmX


main :: IO ()
main = hspec $ do
   describe "Parsing extended nominal terms" $ do
     describe "Parsing a term" $ do
      context "parsing an atom term" $ do
        it "prints atom" $ do
          runParserX parseTrm "[a] 'f ([a->b]^(a b)+X,c)" `shouldBe` Right (AbsTrm "a"(AppTrm "f"))
