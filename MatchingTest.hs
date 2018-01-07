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
                 , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , E (AtmTrm "c") (AtmTrm "d")]
                 , [E (VarTrm (M.fromList []) [] "X") (AtmTrm "d") , F (AtmTrm "a") (VarTrm (M.fromList []) [] "X")]
                 , [E (VarTrm (M.fromList []) [] "X") (AtmTrm "d"), E (AtmTrm "c") (AtmTrm "d") ]
                 ])

      context "when applied to an atom and a variable term" $ do
        it "Returns a set of problems" $ do
          psi (AtmTrm "a") (VarTrm (M.fromList [("c", AtmTrm "a"),("b", (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"))] ) [("a","b")] "X") [] (S.fromList ["a","b","c"])
          `shouldBe` ( S.fromList [
                          [ F (AtmTrm "a") (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"),  F (AtmTrm "a") (AtmTrm "a")]
                          , [F (AtmTrm "a") (AtmTrm "a") , F (AtmTrm "a") (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"), F (AtmTrm "a") (AtmTrm "c")]
                          , [F (AtmTrm "a") (AtmTrm "a") , F (AtmTrm "a") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "c") (VarTrm (M.fromList []) [] "X")]
                          , [F (AtmTrm "a") (AtmTrm "a") , F (AtmTrm "a") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "a") (AtmTrm "a")]
                          , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "a") (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"),  F (AtmTrm "a") (AtmTrm "a")]
                          , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "a") (VarTrm (M.fromList [("a", AtmTrm "b")]) [("a","c")] "Y"), F (AtmTrm "c") (VarTrm (M.fromList []) [] "X")]
                          , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "b") (VarTrm (M.fromList []) [] "X"),  F (AtmTrm "a") (AtmTrm "a")]
                          , [F (AtmTrm "b") (VarTrm (M.fromList []) [] "X") , F (AtmTrm "b") (VarTrm (M.fromList []) [] "X"),  F (AtmTrm "a") (VarTrm (M.fromList []) [] "X")]
                          ])
      describe "Auxiliary Function cap" $ do
        context "when applied to an empty set and a term" $ do
          it "returns the term as a singleton set." $ do
            cap S.empty (AbsTrm "a" (AtmTrm "b")) `shouldBe` S.fromList [AbsTrm "a" (AtmTrm "b")]
            
        context "when applied to a singleton set of atm terms and a term which does not contain VarTrm as subterm" $ do
          it "returns a set of cap terms." $ do
            cap (S.fromList [AtmTrm "a"]) (AppTrm "f" (TplTrm [AbsTrm "a" (AtmTrm "b"), AbsTrm "b" (AtmTrm "c")])) `shouldBe` S.fromList [AppTrm "f" (TplTrm [AbsTrm "a" (AtmTrm "b"), AbsTrm "b" (AtmTrm "c")])] 

        context "when applied to a set of atm terms and a term which does not contain VarTrm as subterm" $ do
          it "returns a set of cap terms." $ do
            cap (S.fromList [AtmTrm "a", AtmTrm "b"]) (AppTrm "f" (TplTrm [AbsTrm "a" (AtmTrm "b"), AbsTrm "b" (AtmTrm "c")])) `shouldBe` S.fromList [AppTrm "f" (TplTrm [AbsTrm "a" (AtmTrm "b"), AbsTrm "b" (AtmTrm "c")])]

        context "when applied to a singleton set of atm terms and a var term with a single a-substitution" $ do
          it "returns a set of cap terms." $ do
            cap (S.fromList [AtmTrm "a"]) (VarTrm (M.fromList [("b", AbsTrm "c" (AtmTrm "d"))]) [("a","b")] "X") `shouldBe` S.fromList [AtmTrm "a", VarTrm (M.fromList []) [("a","b")] "X", VarTrm (M.fromList [("b", AtmTrm "a")]) [("a","b")] "X", VarTrm (M.fromList [("b", AbsTrm "c" (AtmTrm "a"))]) [("a","b")] "X", VarTrm (M.fromList ([("b", AbsTrm "c" (AtmTrm "d"))])) [("a","b")] "X" ]

     describe "General Matching algorithm" $ do
       context "when applied to an empty problem" $ do
         it "returns solution [({{}}, Id)]" $ do
           ( showSols  $  solveMatch S.empty []) `shouldBe` "[({{}}, Id)]"
           
       context "when applied to matching problem populated with consistent freshness constraints" $ do
         it "returns solution [(Delta, Id)] where Delta is a freshness context" $ do
           (showSols  $  solveMatch S.empty [ F (AtmTrm "a") (VarTrm (M.fromList [("b", AtmTrm "c")]) [("b","c")] "X") ] ) `shouldBe` "[({{a#X}, {a#X,c#X}}, Id)]"

       context "when applied to matching problem populated with one or more inconsistent freshness constraints" $ do
         it "returns solution [] " $ do
           (showSols  $  solveMatch S.empty [ F (AtmTrm "a") (AtmTrm "a") ]) `shouldBe` "[]"

       context "when applied to a solvable singleton matching problem  except variable term in the pattern" $ do
         it "returns solution [Delta, Id)] where Delta is a freshness context" $ do
           (showSols  $  solveMatch S.empty [ E (TplTrm [AbsTrm "a" (AtmTrm "b"), AppTrm "'f" (AtmTrm "b")]) (TplTrm [AbsTrm "a" (AtmTrm "b"), AppTrm "'f" (AtmTrm "b")])  ] ) `shouldBe` "[({{}}, Id)]"
