module UnificationX where

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


--unification
unif :: FreshAtms -> VSub -> Prob -> Prob -> (Vsub,S.Set (Maybe Ctx))
unif as sb fc [] 
  =  let (as',prob)=vsb2Constr as sb fc
      in (sb, frsh prob)
unif as sb fc (E (AtmTrm a) (AtmTrm b):xs) | a == b
  =  unif as sb fc xs
unif as sb fc (E (AbsTrm a s) (AbsTrm b t):xs) | a==b
  =  unif as sb fc  (E s t:xs)
unif as sb fc (E (AbsTrm a s) (AbsTrm b t):xs)
  = unif as sb (F (AtmTrm b) s:fc)  (E (prmTrmApp [(a,b)] s) t:xs)
unif as sb fc (E (AppTrm f s) (AppTrm g t):xs) | f==g
  =  unif as sb fc (E s t:xs)
unif as sb fc  (E (TplTrm s) (TplTrm  t):xs) | length s == length t
  = unif as sb fc (zipWith E s t ++xs)
unif as sb fc (E (VarTrm asb p x) (VarTrm asb' p' y):xs) | x==y
  =  let fcs= diffSet atmlist asb asb' p p'--must apply vsub to each a-sub, sequentially
         atmlist  = S.toList $ S.union (atmActDom asb p) (atmActDom asb' p')
         (vsb,ctxs) = unif as sb fc xs
     in  (vsb , (!$ ctxs) `sqUnion` fcs)
unif as sb fc (E s@(VarTrm asb  p x) t:xs)| asb == M.empty
  = if  x `S.member` varsTrm t --better to take out, consumes lots
      then (sb, returnD Nothing) 
        else  unif as' sb' fc prob
            where  sb'= M.insert x (prmTrmApp (prmInv p) t) sb
                   (as',prob)= vsb2Constr as sb' xs
unif as sb fc (E t s@(VarTrm asb _ x):xs) | asb==M.empty
  = unif as sb fc (E s t:xs)
unif as sb fc (c@(E t s):xs)| isVarTrm t || isVarTrm s
  = unif as sb fc (xs++[c])
unif _ sb _ (_:xs) = (sb,  returnD Nothing)


--postponed constraints--to check before starting
isVarTrm:: Trm->Bool
isVarTrm (VarTrm{}) =True
isVarTrm _ =False

--applies vsub and resolves freshness
solveDiffSet:: FreshAtms -> VSub -> S.Set (Maybe Ctx) -> Ctxs -> Ctxs
solveDiffSet atms sb s c
             = let fatms = frshGen (S.unions [fst atms, atmsVSub sb ,atmsCtxs c])
                   resolve = foldrD S.union (returnD S.empty) . 
                            fnD (solveAlpha . snd . vsb2Constr fatms sb . ctx2Constr) . toD
               in S.union c (resolve s)


--main function to solve unification, snd in FreshAtms is empty to start w
--so only sorted if necessary
solveUnif :: Prob ->  Sol
solveUnif p
    = let  (vsb,mCtx) = unif (atmsProb p,S.empty) M.empty [] p
      in (vsb, toD mCtx)

--pattern unif
solvePatUnif::  Ctx -> Prob ->  Sol
solvePatUnif ctx prob
    = let (vsb,mCtx) = unif (atmsCtx ctx `S.union` atmsProb prob,S.empty) M.empty (ctx2Constr ctx) prob
      in (vsb, toD mCtx)

