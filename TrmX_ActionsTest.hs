module TrmX_ActionsTest where

import Test.Hspec
import TrmX
import TrmX_Actions
import qualified Data.Map as M
import qualified Data.Set as S


main :: IO ()
main = hspec $ do
  describe "TrmX_Actions" $ do
     describe "prmComp" $ do
       it "returns a composition of a pair of permutations p1 p2 such that p1.p2 and applied from lhs to rhs" $
         prmComp [("a", "b")] [("a" ,"c"),("d" ,"e")] `shouldBe` ([("a" ,"b"),("a" ,"c"),("d" ,"e")]::Prm)

     describe "prmAtmApp" $ do
       it "applies a permutation to an atom" $
         prmAtmApp  [("a" ,"c"),("c" ,"e")] "a" `shouldBe` ("e"::Atm)
         
     describe "prmAsbApp" $ do
       context "when provided with an empty mapping of atm substitutions" $ do
          it " it returns the empty mapping" $
             prmAsbApp [("a" ,"c"),("d" ,"e")] (M.fromList ([])) `shouldBe` (M.fromList ([]))
       context "when provided with an empty permutation" $ do
          it " it returns the mapping without identity mappings" $
             prmAsbApp [] (M.fromList ([("a",AtmTrm "a"),("b",AtmTrm "c")])) `shouldBe` (M.fromList ([("b",AtmTrm "c")]))
       context "when provided with a permutation and a mapping" $ do
         it " it returns the permuted mapping without identity mappings" $
            prmAsbApp [("a" ,"c"),("d" ,"e")] (M.fromList ([("a",AtmTrm "a"),("c",AtmTrm "d")])) `shouldBe` (M.fromList ([("a",AtmTrm "e")]))

            
     describe "prmTrmApp" $ do
       it "applies a permutation to a term; identity mappings of atm substitutions are removed" $
         prmTrmApp  [("a" ,"c"),("c" ,"e")] (AppTrm "f" (TplTrm [AtmTrm "a", AbsTrm "c" (VarTrm (M.fromList ([("a",AtmTrm "a"),("c",AtmTrm "e")]))  [("a", "b")] "X")])::Trm) `shouldBe`(AppTrm "f" (TplTrm [AtmTrm "e", AbsTrm "a" (VarTrm (M.fromList ([("a",AtmTrm "c")]))  [("a", "b"),("a" ,"c"),("c" ,"e")] "X")])::Trm)

     describe "prmSupp" $ do
       it "returns the support of a permutation p, ie., {a | p(a) /= a, a <- p}." $
         prmSupp  [("c","e"),("a","a"),("b" ,"d"),("c" ,"e")]  `shouldBe` (S.fromList ["b","d"])

     describe "prmDs" $ do
       it "Returns the Difference Set between a pair of permutations, that is, for permutations p,p' and atom a, if p(a)=b and p'(a)=c, for any two distinct atoms b,c, then atom a is in their Difference set." $
         prmDs  [("c","e"),("e" ,"d")] [("c","d"), ("e","f")]  `shouldBe` (S.fromList ["d","e","f"])

     describe "aSbDom" $ do
       it "Returns the set of atoms in the domain of atm subst mappings; excludes identity mappings." $
         aSbDom (M.fromList ([("a",AtmTrm "a"),("c",AtmTrm "d")])) `shouldBe` (S.fromList ["c"])
         


     describe "aSbImg" $ do
       it "Returns the image of atm subst mappings; excludes identity mappings." $
         aSbImg (M.fromList ([("a",AtmTrm "a"),("b",AtmTrm "d"), ("c",AbsTrm "d" (AtmTrm "c"))])) `shouldBe` (S.fromList [AtmTrm "d", AbsTrm "d" (AtmTrm "c")])

         
     describe "atmActDom" $ do
       it "Returns the set of atoms in the domain; excludes identity mappings." $
         atmActDom (M.fromList ([("a",AtmTrm "a"),("c",AtmTrm "d")])) [("c","e"),("a","a"),("b" ,"d"),("c" ,"e")] `shouldBe` (S.fromList ["c","b","d"])

         
     describe "ctxGen" $ do
       it "Generates a freshness context given a set of atoms and a set of variables." $
         ctxGen (S.fromList (["a","b"])) (S.fromList (["X","Y"])) `shouldBe` (S.fromList [("a","X"), ("b", "X" ), ("a","Y"), ("b","Y")])
