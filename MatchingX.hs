module MatchingX where

import TrmX
import ConstraintsX
import AlphaX
import Asb
import Freshen
import SetofSets
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
--import qualified Data.Maybe as MB
import qualified Control.Monad as C
import qualified Control.Applicative as A


--matching. 2 options, returning frshAtms or not
match :: FreshAtms -> VSub -> Prob -> Prob -> Maybe Sol
match as sb fc [] 
  =  let (as',prob)=vsb2Constr as sb fc 
         ctxs= solveAlpha prob
     in if S.null ctxs then Nothing else Just (sb,ctxs)
match as sb fc (E (AtmTrm a) (AtmTrm b):xs) | a == b
  =  match as sb fc xs
match as sb fc (E (AbsTrm a s) (AbsTrm b t):xs) | a==b
  =  match as sb fc  (anEConstr s t:xs)
match as sb fc (E (AbsTrm a s) (AbsTrm b t):xs)
  = match as sb (aFConstr (AtmTrm a) t:fc)  (anEConstr s (prmTrmApp [(a,b)] t):xs)
match as sb fc (E (AppTrm f s) (AppTrm g t):xs) | f==g
  =  match as sb fc (anEConstr s t:xs)
match as sb fc  (E (TplTrm s) (TplTrm  t):xs) | length s == length t
  = match as sb fc (zipWith anEConstr s t ++ xs)
match as sb fc (E (VarTrm asb p x) (VarTrm asb' p' y):xs) | x==y
  = case match as sb fc xs of
         Nothing -> Nothing
         Just (vsb, ctxs) -> let fcs= solveDiffSet as vsb diffSet ctxs
                             in if S.null fcs then Nothing else Just (vsb,fcs)
    where diffSet = sqUnions (map (\a-> auxFn x a (anEConstr (atmActAtm asb p  a) (atmActAtm asb' p' a)))
                              (S.toList $ S.union (atmActDom asb p) (atmActDom asb' p') ))
match as sb fc (E s@(VarTrm asb  p x) t:xs)| asb == M.empty
  = if  x `S.member` varsTrm t
      then Nothing 
        else  match as' sb' fc prob
            where  sb'= M.insert x (prmTrmApp (prmInv p) t) sb
                   (as',prob)= vsb2Constr as sb' xs
match as sb fc (c@(E t s):xs)| isVarTrm t
  = match as sb fc (xs++[c])
match _ _ _ (_:xs) =  Nothing


--postponed constraints--to check before starting
isVarTrm:: Trm->Bool
isVarTrm (VarTrm{}) =True
isVarTrm _ =False

--applies vsub and resolves freshness
solveDiffSet:: FreshAtms -> VSub -> S.Set (Maybe Ctx) -> Ctxs -> Ctxs
solveDiffSet atms sb s c
             = let fatms = frshGen (S.unions [fst atms, atmsVSub sb,atmsCtxs c])
                   resolve = foldrD S.union (returnD S.empty) . 
                              fnD (solveAlpha . snd . vsb2Constr fatms sb . ctx2Constr) . toD
               in S.union c (resolve s)


--main function to solve matching. local version for freshAtms and global

      
-- matching local fresh variables
solveMatch::   Prob -> Maybe Sol
solveMatch  prob
    = match ( atmsProb prob ,S.empty) M.empty [] prob

-- matching global fresh variables
solveMatch':: FreshAtms->  Prob -> Maybe Sol
solveMatch' atms
    = match atms  M.empty []