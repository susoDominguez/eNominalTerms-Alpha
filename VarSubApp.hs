---------------------------Vsub app
module VarSubApp where

--vsubApp must be with atmSub because aSbApp may be initiated after an instantiation

type ErrCtx = String

{-| vsbSearch looks for a particular variable instance returning Just Trm or NOthing otherwise.-}
vsbSearch :: Var -> VSub -> Maybe Trm
vsbSearch  = M.lookup

{-| action of Var Subs on a Term. A freshness context is needed because of potential atom
  substitutions. If freshnesses are not satisfied, it returns an error. -}
vsubApp :: Ctx -> VSub -> Trm -> Either ErrCtx Trm
vsubApp fc vsb t@(VarTrm asb p x) =
  = case vsbSearch x vsb of
     Nothing -> t
     Just s  -> if satisfyCtx 
         where act fc asb p = aSbApp fc asb . prmTrmApp p
vsubApp fc vsb (AppTrm f t)=  AppTrm f (vsubApp fc vsb t)
vsubApp fc vsb (TplTrm ts)= L.map (vsubApp fc vsb) ts
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

--apply both perm and asubs to a term
atmActionsTrm fc asb p = aSbApp fc asb . prmTrmApp p



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
