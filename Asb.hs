module Asb where

import TrmX
import Freshen2
import ConstraintsX
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow

-------------------------------------------------------------------------
{-atom 2 term subst:   garbage collector on ID atm subs for each action-}

--Composition of atm sub
aSbComp::InAtms -> Asb -> Asb -> (InAtms, Ctx, Asb) -- composition of atm subs
aSbComp frsh sb1 sb2 =
  let (frsh', sb1')  = M.mapAccum (\acc v -> aSbApp acc sb2 v) frsh sb1
      ks = M.keys sb1'
      (ctxs, trms)= unzip $ M.elems sb1'
      step3 k v = aSbFiltr . M.fromList $  zip k v
  in (frsh' ,S.unions ctxs  , step3 ks trms `M.union`  sb2) --union left-biased so it works
       

--delete an entry from Dictionary
aSbDel:: Atm -> Asb -> Asb
aSbDel  = M.delete

-- application of atm subst to an atom, return atm itself as Trm if not found
aSbAtmApp:: Asb -> Atm -> Trm
aSbAtmApp sb a =  M.findWithDefault (anAtmTrm a) a sb


--application of atms subst to terms; returns ctx too
aSbApp:: InAtms -> Asb -> Trm  -> (InAtms, TrmCtx)
aSbApp  atms asb  t | M.null asb =
  (atms, (S.empty, t)) --empty assumptions
aSbApp atms sb  (AtmTrm a) =
  (atms,(S.empty, aSbAtmApp sb a))
aSbApp atms sb2 (VarTrm sb1 p x) =
  let (atms', ctx, asb) = aSbComp atms sb1 sb2
  in (atms', (ctx, aVarTrm asb p x))
aSbApp atms asb abs@(AbsTrm a t)| a `M.member` asb =
  aSbApp atms (aSbDel a asb) abs
aSbApp atms asb (AbsTrm a t) =
  (frsh2, (fc `S.union` ctx, AbsTrm newAtm trm))
    where (frsh,newAtm)= frshen atms a
          (frsh2,(ctx,trm))= aSbApp frsh asb (prmTrmApp [(newAtm, a)] t)
          fc = ctxGen (S.singleton newAtm) (varsAsb asb `S.union` varsTrm t)
aSbApp atms asb (AppTrm f t) =
  let (frsh,(ctx,trm)) = aSbApp atms asb t
  in  (frsh, (ctx, AppTrm f trm))
aSbApp atms asb (TplTrm ts) =
  let (frsh', (fc',ts')) = second unzip $ L.mapAccumL (\acc t -> aSbApp acc asb t) atms ts
  in (frsh',(S.unions fc', TplTrm ts'))


---------------------------
--Vsub app

--vsubApp must be with atmSub

vsbSearch :: Var -> VSub -> Maybe Trm
vsbSearch  = M.lookup

--action of VSb
vsubApp :: InAtms -> VSub -> Trm ->(InAtms, TrmCtx) 
vsubApp atms vsb t@(VarTrm asb p x)
  = case vsbSearch x vsb of
     Nothing -> (atms,(S.empty, t))
     Just s  -> let atms' = atmsTrm s
                in atmActions (atms `S.union` atms') asb p s
vsubApp atms vsb (AppTrm f t)
  = let (frsh,(ctx,trm))= vsubApp atms vsb t
    in (frsh, (ctx, AppTrm f trm))
vsubApp atms vsb (TplTrm ts)
  = let (frsh, (ctx, ts')) = second unzip $ L.mapAccumL (\acc t -> vsubApp acc vsb t) atms ts
    in (frsh, (S.unions ctx, TplTrm ts'))
vsubApp atms vsb (AbsTrm a t)
  =  let (frsh,(ctx,trm))= vsubApp atms vsb t
     in (frsh, (ctx, AbsTrm a trm))
vsubApp atms _ t = (atms,(S.empty,t))



-- idempotent substitution composition: see baader & snyder
vsubComp ::InAtms -> VSub -> VSub -> (InAtms, Ctx, VSub)
vsubComp atms sb1 sb2
 = (frsh , S.unions ctxs , step3 (step1  ks trms) `M.union`  sb2)
    where (frsh, sb1') = M.mapAccum (\acc t -> vsubApp acc sb2 t) atms sb1
          (ctxs,trms) = unzip $ M.elems sb1'
          ks = M.keys sb1'
          step1 k v= M.fromList $ zip k v 
          step3 = M.filterWithKey (\v t -> aVarTrm M.empty [] v /= t) --discard Id vsbs

--apply both perm and asubs
atmActions atms asb p = aSbApp atms asb . prmTrmApp p

--apply both actions to an atm
atmActAtm asb p = aSbAtmApp asb . prmAtmApp p

--------------------------------------------
----------------------------------------------
--vsubApp for Constr data structure
vsubCnApp:: InAtms -> VSub -> Constr Trm -> (InAtms, Prob)
vsubCnApp fAtm vsb c
 = (fAtm'', if isEConstr c 
             then anEConstr tL tR:ctx
              else aFConstr tL tR:ctx)
 where fn a = vsubApp a vsb
       (fAtm',(fcL,tL)) = fn fAtm (getL c)
       (fAtm'',(fcR,tR)) = fn fAtm' (getR c)
       ctx= ctx2Constr (fcL `S.union` fcR)


--vsubApp for a problem, requires 2 functions. vsb2Constr is the main one
vsubCnsApp as vsb prob = second concat $ L.mapAccumL (\acc p -> vsubCnApp acc vsb p) as prob 

--vsb2Constr:: InAtms -> VSub -> Prob -> (InAtms,Prob)
--vsb2Constr f v p = let (f',p')= unzip $ vsubCnsApp f v p
  --                 in (f', second concat p')
