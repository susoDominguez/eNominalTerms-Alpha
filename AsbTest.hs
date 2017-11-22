module AsbTest where

import Test.Hspec
import TrmX
import ConstraintsX
import MatchingX
import TrmX_Actions
import Asb
import qualified Data.Map as M
import qualified Data.Set as S


main :: IO ()
main = hspec $ do
  describe "Atom substitution application" $ do
    describe "Atom substitution applied to an atom: aSbAtmApp" $ do
      context "when applied to an atom not in the domain of atm mappings" $ do
        it "Returns the atom itself as an atom term" $ do
          aSbAtmApp (M.fromList [("b", AppTrm "f" (TplTrm [])),("c", AtmTrm "c"), ("d", AtmTrm "g")]) "a" `shouldBe` AtmTrm "a"

      context "when applied to an atom in the domain of atm mappings" $ do
        it "Returns the image term of such atom" $ do
          aSbAtmApp (M.fromList [("b", AppTrm "f" (TplTrm [])),("c", AtmTrm "c"), ("d", AtmTrm "g")]) "b" `shouldBe` AppTrm "f" (TplTrm [])

    describe "aSbApp" $do
      context "when, given a freshness context, atom substituion applied to term with no variable subterms containing no matching atoms from the atm substitution domain" $ do
        it "returns a pair of the same freshness context and the same term." $ do
          aSbApp (S.fromList [("c","X")], S.fromList ["m","n","o","p","q","r", "s"]) (M.fromList [("b", AppTrm "f" (TplTrm [])) , ("c", AtmTrm "b") , ("d", AtmTrm "g")]) (TplTrm [AppTrm "f" (TplTrm [AtmTrm "a'"]), AtmTrm "a"]) `shouldBe` ((S.fromList [("c","X")], S.fromList ["m","n","o","p","q","r", "s"]),TplTrm [AppTrm "f" (TplTrm [AtmTrm "a'"]), AtmTrm "a"])
      context "when, given a freshness context, atom substituion applied to Variable term containing no matching atoms from the atm substitution domain" $ do
        it "returns a pair of the same freshness context and the modified term with a composition of atm substitutions suspended over the variable symbol where Identity mappings are discarded and the atm substitutions mappings given as a parameter have been applied to the image of the atom substitutions initially suspended over the variable symbol." $ do
          aSbApp (S.fromList [("c","X")], S.fromList ["m","n","o","p","q","r", "s"]) (M.fromList [("b", AppTrm "f" (TplTrm [])) , ("c", AtmTrm "c") , ("d", AtmTrm "g")]) (VarTrm (M.fromList [("a",AppTrm "g" (TplTrm [AtmTrm "b"])),("b", AtmTrm "a"), ("c" ,AtmTrm "c")]) [("a","b")] "X") `shouldBe` ((S.fromList [("c","X")], S.fromList ["m","n","o","p","q","r", "s"]), VarTrm (M.fromList [("d", AtmTrm "g"),("a", AppTrm "g" (TplTrm [AppTrm "f" (TplTrm [])]) ),("b", AtmTrm "a")]) [("a","b")] "X")
          
      context "when, given a freshness context, atom substituion applied to term containing atoms which match those in the domain of the atom substitution. Case for a term with no abstraction subterms" $ do
        it "returns a pair of the same freshness context and the modified term." $ do
          aSbApp (S.fromList [("c","X")], S.fromList ["m","n","o","p","q","r", "s"]) (M.fromList [("b", AppTrm "f" (TplTrm [])) , ("c", AtmTrm "b") , ("d", AtmTrm "g")]) (TplTrm [AppTrm "b" (TplTrm [VarTrm (M.fromList []) [("a","b")] "X"]), AtmTrm "b"]) `shouldBe` ((S.fromList [("c","X")], S.fromList ["m","n","o","p","q","r", "s"]), TplTrm [AppTrm "b" (TplTrm [VarTrm (M.fromList [("b", AppTrm "f" (TplTrm [])) , ("c", AtmTrm "b") , ("d", AtmTrm "g")]) [("a","b")] "X"]), AppTrm "f" (TplTrm [])])

      context "when, given a freshness context, atom substitution applied to abstraction term" $ do
        it "returns a pair of a freshness context  and the modified abstraction term where the context has less new atoms to chose from, additional primitive constraints (a,X) where X represents vars occurring in the abstraction term and the image of atom substitutions and atom a  is a fresh atom for both the abstraction term and the image of atom substitutions" $ do
          aSbApp (S.fromList [("c","X")], S.fromList ["m","n","o","p","q","r", "s"]) (M.fromList [ ("c", AtmTrm "b") , ("d", AtmTrm "g")]) (AbsTrm "a" (AbsTrm "b" (AbsTrm "c" (TplTrm [AtmTrm "c",AtmTrm "a", AtmTrm "d", VarTrm (M.fromList [("a", VarTrm (M.fromList []) [] "Z" )]) [] "Y"]) ))) `shouldBe`  ((S.fromList [("c","X"),("m","Y"),("m","Z"),("n","Y"),("n","Z"),("o","Y"),("o","Z")], S.fromList ["p","q","r", "s"]), (AbsTrm "m" (AbsTrm "n" (AbsTrm "o" (TplTrm [AtmTrm "o", AtmTrm "m", AtmTrm "g", VarTrm (M.fromList [("m", VarTrm (M.fromList [("c", AtmTrm "b") , ("d", AtmTrm "g")]) [("m","a"),("n","b"),("o","c")] "Z" ),("c", AtmTrm "b") , ("d", AtmTrm "g")]) [("m","a"),("n","b"),("o","c")] "Y"]) ))))
