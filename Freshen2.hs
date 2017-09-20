module Freshen2 where

import TrmX
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Char as C
import Control.Arrow
--------------------------------------------------------------------------------------------
type InAtms = S.Set Atm
type InVrs = S.Set Var
type RnmMap = M.Map String String

---------------------------------------------------------------------------
--Freshen rules and Terms

--freshen rule w/respect to itself and trmCtx, but trmCtx is untouched
freshenRnT:: Rule -> TrmCtx -> Rule
freshenRnT rl t =
  let atms = atmsRl rl  
      vrs = varsRl rl
      (f1,atmsM) = frshenM (atms `S.union` atmsTrmCtx t) (M.fromSet id atms)
      (f2,vrsM) =  frshenM (vrs `S.union` varsTrmCtx t) (M.fromSet id vrs)
  in renameAtmRl atmsM $ renameVarRl vrsM rl

freshenRl:: Rule -> Rule
freshenRl rl  =
  let atms = atmsRl rl  
      vrs = varsRl rl
      (f1,atmsM) = frshenM atms (M.fromSet id atms)
      (f2,vrsM) =  frshenM vrs (M.fromSet id vrs)
  in renameAtmRl atmsM $ renameVarRl vrsM rl

freshenTFc:: TrmCtx  -> TrmCtx
freshenTFc s  =
  let atms = atmsTrmCtx s  
      vrs = varsTrmCtx s
      (f1,atmsM) = frshenM atms (M.fromSet id atms)
      (f2,vrsM) =  frshenM vrs  (M.fromSet id vrs)
  in renameAtmTrmCtx atmsM $ renameVarTrmCtx vrsM s

freshenT:: Trm  -> Trm
freshenT s  =
  let atms = atmsTrm s  
      vrs = varsTrm s
      (f1,atmsM) = frshenM atms (M.fromSet id atms)
      (f2,vrsM) =  frshenM vrs  (M.fromSet id vrs)
  in renameTrm atmsM $ renameTrm vrsM s

--rename Vars in rules before matching.needed for standard? rewriting.
--context not added-> RuleValidity
freshenVars:: Rule -> Trm -> Rule
freshenVars rl  t = 
  let vrs = varsRl rl
      (f,vrsM) =  frshenM (varsTrm t) (M.fromSet id vrs) --rename only if also in trm
  in  renameVarRl vrsM rl

-------------------------------------------------------------------------------
--Renaming for closed rules, RnmMap is built prior exec, applied both to atms n vars

--both for Atms and Vars
rename ::RnmMap -> String -> String
rename m a = M.findWithDefault a a m

renamePrm :: RnmMap -> Prm -> Prm
renamePrm m = map (rename m *** rename m) 

renameAsb :: RnmMap -> Asb -> Asb
renameAsb m = M.map (renameTrm m) . M.mapKeys (rename m) 

renameAtmCtx :: RnmMap  -> Ctx -> Ctx
renameAtmCtx m = S.map (first (rename m))

renameVarCtx :: RnmMap -> Ctx -> Ctx
renameVarCtx m = S.map (second (rename m))

renameTrm :: RnmMap -> Trm -> Trm
renameTrm m (AtmTrm a)   = AtmTrm (rename m a)
renameTrm m (AbsTrm a t) = AbsTrm (rename m a) (renameTrm m t)
renameTrm m (AppTrm f t) = AppTrm f (renameTrm m t)
renameTrm m (TplTrm ts)  = TplTrm (map (renameTrm m) ts)
renameTrm m (VarTrm asb  p v) = VarTrm (renameAsb m asb) (renamePrm m p) (rename m  v)

renameAtmRl :: RnmMap -> Rule -> Rule
renameAtmRl m (fc,l,r) = (fc',l',r')
  where fc' = renameAtmCtx m fc
        l'  = renameTrm m l
        r'  = renameTrm m r 

renameVarRl :: RnmMap -> Rule -> Rule
renameVarRl m (fc,l,r) = (fc',l',r')
  where fc' = renameVarCtx m fc
        l'  = renameTrm m l
        r'  = renameTrm m r

renameAtmTrmCtx :: RnmMap -> TrmCtx -> TrmCtx
renameAtmTrmCtx ns (fc, t) = (fc', t')
    where fc' = renameAtmCtx ns fc
          t' = renameTrm ns t

renameVarTrmCtx :: RnmMap -> TrmCtx -> TrmCtx
renameVarTrmCtx ns (fc, t) = (fc', t')
    where fc' = renameVarCtx ns fc
          t' = renameTrm ns t

frshenM :: S.Set String -> RnmMap -> (S.Set String, RnmMap)
frshenM s m = M.mapAccum frshen s m --unsure,test it works as expected

frshen :: S.Set String -> String -> (S.Set String, String)
frshen s m = let a = aNewNm s m
             in (s `S.union` S.singleton a, a)

--recursively builds a fresh Atm or new Var, it stops when it's not in set of current ones
aNewNm :: S.Set String -> String -> String
aNewNm s a
  | a `S.member` s = aNewNm s (if C.isDigit l then d ++ fn l else a ++ "0" )
  | otherwise = a --base case
  where  l = last a --last digit/letter
         d = init a --all but last, empty if only 1 char
         fn =  show .  (1 +) . C.digitToInt
