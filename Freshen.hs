module Freshen where

import TrmX
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Char as C

--------------------------------------------------------------------------------------------



{-Wrappers-}
{-Function that genenerates new freshness constraints from old ones-}

frshGen ::Set Atm -> FreshAtms
frshGen atms = (atms, testSize atms (newNames atms))


frshAtmGen ::  TrmCtx -> S.Set Atm
frshAtmGen t =  testSize (atmsTrmCtx t) (newNames (atmsTrmCtx t))

frshVarGen ::  Trm -> S.Set Var
frshVarGen t =  testSize (varsTrm t) (newNames (varsTrm t))

--parses an atom f an atmSet and adds a number: returns dif set from original atms
newNames:: S.Set String -> S.Set String
newNames atms = S.map aNewName atms S.\\ atms
                                                          
--testSize checks newAtms enough size else acts on itself growing at least size +1
testSize:: S.Set String -> S.Set String -> S.Set String
testSize atms nwAtms = if nwAtms < atms || any (\a-> S.singleton a `S.isSubsetOf` atms) (S.toList nwAtms)
                        then testSize atms $ S.union nwAtms (newNames nwAtms)
                             else nwAtms

--add +1 function
aNewName :: String -> String
aNewName a = if C.isDigit l then d ++ [x] else a ++ "0"  
               where   l = last a
                       d = init a
                       x = C.intToDigit .  (1 +) $ C.digitToInt l

--pick an atom from set of avail ones else create new ones
pickAtm::FreshAtms -> (FreshAtms,Atm)
pickAtm (old,new) = if S.null new
                    then pickAtm (frshGen old)
                         else ((S.insert atm old,S.delete atm new),atm)
                              where atm=if S.size new `mod` 2 == 0
                                           then S.elemAt (S.size new -1) new
                                                else S.elemAt 0 new
--maybe do a pickAtmWith::atm->freshAtms
                                    
--theres a chance of repetition in tuples but not clashing of binders
unionFrshAtms:: FreshAtms -> FreshAtms -> FreshAtms
unionFrshAtms (old1, new1) (old2, new2) = let olds=  old1 `S.union` old2
                                              news=  new1 `S.union` new2
                                          in (olds, news S.\\ olds)

unionsFrshAtms= foldr unionFrshAtms (S.empty,S.empty) 

---------------------------------------------------------------------------
--Freshen rules and Terms

--freshen rule w/respect to itself and trmCtx, but trmCtx is untouched
freshenRnT:: Rule -> TrmCtx -> Rule
freshenRnT (fc, l ,r) (ctx, t) = let atmPairs = zip (S.toList $ atmsTrmCtx (S.union ctx fc,TplTrm [l,r,t])) (S.toList $ frshAtmGen ( ctx `S.union` fc,TplTrm [l,r,t]))
                                     varPairs = zip (S.toList $ varsTrm (TplTrm [l,r,t])) (S.toList $ frshVarGen (TplTrm [l,r,t]))
                                 in (freshCtx atmPairs varPairs fc, freshT atmPairs varPairs l,freshT atmPairs varPairs r )


freshenR:: Rule  -> Rule
freshenR (fc, l ,r)  = let atmPairs = zip (S.toList $ atmsTrmCtx ( fc,TplTrm [l,r])) (S.toList $ frshAtmGen (fc,TplTrm [l,r]))
                           varPairs = zip (S.toList $ varsTrm (TplTrm [l,r])) (S.toList $ frshVarGen (TplTrm [l,r]))
                       in (freshCtx atmPairs varPairs fc, freshT atmPairs varPairs l,freshT atmPairs varPairs r )

freshenTFc:: TrmCtx  -> TrmCtx
freshenTFc s  = let atmPairs = zip (S.toList $ atmsTrmCtx s) (S.toList $ frshAtmGen s)
                    varPairs = zip (S.toList . varsTrm $ snd s) (S.toList . frshVarGen $ snd s)
                       in (freshCtx atmPairs varPairs Control.Arrow.***
                            freshT atmPairs varPairs)

freshenT:: Trm  -> Trm
freshenT s  = let atmPairs = zip (S.toList $ atmsTrm s) (S.toList $ frshAtmGen (S.empty,s))
                  varPairs = zip (S.toList $ varsTrm s) (S.toList $ frshVarGen s)
                    in  freshT atmPairs varPairs  s

--rename Vars in rules before matching.needed for standard rewriting.context not added->RuleValidity
freshenVars:: Rule -> Trm -> Rule
freshenVars (fc, l ,r)  t = let varPairs = zip (S.toList $ varsTrm (TplTrm [l,r,t])) (S.toList $ frshVarGen (TplTrm [l,r,t]))
                               in (freshCtx  [] varPairs fc, freshT [] varPairs l,freshT [] varPairs r )

-------------------------------------
-- Renaming fun. input as follows: atmPairs varPairs Trm
freshT :: [(Atm,Atm)] ->  [(Var,Var)]-> Trm -> Trm
freshT as vrs t = foldr renameAtmTrm (foldr renameVarTrm t vrs) as

freshCtx :: [(Atm,Atm)] ->  [(Var,Var)]-> Ctx -> Ctx
freshCtx as vrs fc = foldr renameAtmCtx (foldr renameVarCtx fc vrs) as
