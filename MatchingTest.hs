module MatchingTest where

import Test.Hspec
import TrmX
import ConstraintsX
import MatchingX
import TrmX_Actions
import qualified Data.Map as M
import qualified Data.Set as S


main :: IO ()
main = hspec $ do
  describe "Matching Algorithm For Extended Terms" $ do
    describe "Auxiliary Function psi" $ do
      context "when applied to a pair of variable terms with the same variable symbols" $ do
        it "Returns a set of problems" $ do
          psi (VarTrm (M.fromList [("a", AtmTrm "c"),("b", (VarTrm (M.fromList []) [] "X"))]) [] "X") (VarTrm (M.fromList [("a", AtmTrm "d"),("b",  AtmTrm "d")]) [] "X") [] (S.fromList ["a","b"]) `shouldBe` (S.fromList [                                                                                                             [ F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "a") (VarTrm (M.fromList []) [] "X")]
                 , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , Eq (AtmTrm "c") (AtmTrm "d")]
                 , [Eq (VarTrm (M.fromList []) [] "X") (AtmTrm "d") , F (AtmTrm "a") (VarTrm (M.fromList []) [] "X")]
                 , [Eq (VarTrm (M.fromList []) [] "X") (AtmTrm "d"), Eq (AtmTrm "c") (AtmTrm "d") ]
                 ])

      context "when applied to an atom and a variable term" $ do
        it "Returns a set of problems" $ do
          psi (AtmTrm "a") (VarTrm (M.fromList [("c", AtmTrm "a"),("b", (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"))] ) [("a","b")] "X") [] (S.fromList ["a","c","b"])
          `shouldBe` ( S.fromList [
                          [F (AtmTrm "a") (AtmTrm "a") , F (AtmTrm "a") (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"),  F (AtmTrm "a") (AtmTrm "a")]
                          , [F (AtmTrm "a") (AtmTrm "a") , F (AtmTrm "a") (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"), F (AtmTrm "a") (AtmTrm "c")]
                          , [F (AtmTrm "a") (AtmTrm "a") , F (AtmTrm "a") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "c") (VarTrm (M.fromList []) [] "X")]
                          , [F (AtmTrm "a") (AtmTrm "a") , F (AtmTrm "a") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "a") (AtmTrm "a")]
                          , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "a") (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"),  F (AtmTrm "a") (AtmTrm "a")]
                          , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "a") (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"), F (AtmTrm "c") (VarTrm (M.fromList []) [] "X")]
                          , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "b") (VarTrm (M.fromList []) [] "X"),  F (AtmTrm "a") (AtmTrm "a")]
                          , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "b") (VarTrm (M.fromList []) [] "X"),  F (AtmTrm "a") (VarTrm (M.fromList []) [] "X")]
                          ])
