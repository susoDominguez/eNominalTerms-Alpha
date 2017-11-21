module MatchingX where (solveMatch)

import TrmX
import TrmX_Actions
import ConstraintsX
import Asb
import SetofSets
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Control.Monad as C
import qualified Control.Applicative as A


---AUXILIARY FUNCTIONS----

{-Function psi is applied to handle constraints of the form φˆπ·X ?≈ φ′ˆπ′·X, that is, deals with the premise of rule (≈αX) (see Def.2.4 in the conference paper) in set not ation.-}
psi :: Trm -> Trm -> Prob -> Set Atm -> Set Prob
psi _ _ p S.empty = p
psi v1@(VarTrm sb prm x) v2@(VarTrm sb' prm' x') p atms = --x==x' is tested bf calling psi
  let atm = S.elemAt 0 atms --chosen atom
      atms' = S.deleteAt 0 atms --delete chosen atm from atom set
      eqC = anEConstr (atmActAtm asb p atm) (atmActAtm asb' p' atm) --build EqConstr
      fcC = aFConstr atm (aVarTrm M.empty [] x) --build primitive frshness Constr
  in psi v1 v2 (eqC:p) atms' S.union  psi v1 v2 (fcC:p) atms'--join both rec. paths
psi atmTrm@(AtmTrm a) var@(VarTrm sb prm x) p atms =
  let atm = S.elemAt 0 atms --chosen atom
      atms' = S.deleteAt 0 atms  --delete chosen atm from atom set
      fcC1 = aFConstr atm (aSbAtmApp sb atm)--build frshness Constr
      fcC2 = aFConstr (prmAtmApp (invPrm prm) atm) (aVarTrm M.empty [] x) --build primitive frshness Constr
  in psi atmTrm var (fcC1:p) atms' S.union  psi atmTrm var (fcC2:p) atms'--join both rec. paths


{-Function Cap returns a finite set of terms equivalent to another term t
  everywhere except below some position p_i in t where atoms from an atmSet have
  been inserted instead. enhanced to add subterm \pi.X to set of terms when \phi^\pi.X  is encountered.-}
cap::  Set Trm -> Trm -> Set Trm
cap S.empty t               = t --returns the whole term when no atoms in the set
cap atms atm@(AtmTrm a)     = atms `S.union` atm
cap atms (VarTrm asb prm x) =
  let asb' = L.map (\(a,xs) -> L.map (\x -> (a,x)) xs)  $ M.toList asb -- list of lists sharing same atom in 1st pos of pair (Atm, Trm)
      asbs = L.map M.fromList $ sequence asb' --product of list of lists; cast each to Map
      varSet = S.fromList $ L.map (\sb -> aVarTrm sb prm x) asbs --set of varTrms for each asub mapping
  in  S.insert (aVarTrm M.empty prm x) $ S.union varSet atms
cap atms (AbsTrm a t)       = let ts  = cap atms t
                                  abSet = S.map (anAbsTrm a) ts
                              in  S.union abs atms
cap atms (AppTrm f t)       = let ts = cap atms t
                                  fSet = S.map (anAppTrm f) ts
                              in  S.union fs atms
cap atms (TplTrm ts)        = let ts' = sequence $ L.map (S.toList . (cap atms)) ts
                                  tsSet = S.fromList $ L.map aTplTrm ts'
                              in  S.union tsSet atms


--Matching function following a 2-phase strategy, first equality constraints then freshness constraints. The matching function takes as arguments a set of RHS vars from the given problem, a pair of a freshness context and a set of new atoms with respect to the problem, a variable substitution, a freshness constraint problem and an equality constriant problem. It returns a set of matching solutions of the form (Ctxs,Vsub) where Ctxs may be empty and thus indicating such pair fails to match the given problem.
--Observe that there is no rule for Vars with distinct name, it is subsumed by the variable rule because of the enhancenment done to function Cap.

match :: Set Var -> (Ctx,Set Atm) -> VSub -> Prob -> Prob -> Sols
match vRHS fc@(ctx,nwAs) vsb fcP [] --starts 2nd phase of algorithm
  =  let (fc', fcP') = vsubProbApp fc vsb (fcP ++ ctx2Constr ctx) --convert generated ctx into frshness constraints to apply vsub
         fcP1 = ctx2Constr fc' --convert generated ctx into frsh constr to solve Algor
         ctxs = solveFrsh (fcP' ++ fcP1)
     in S.insert (ctxs,vsb)
match vRHS (ctx,nwAs) vsb fcP (fc@(F _ _ ):xs)
  = match vRHS (ctx,nwAs) vsb (fc:fcP) xs --add to frshness constraint problem
match vRHS (ctx,nwAs) vsb fcP (E s t:xs) | s == t --subsumes atmTrm equality rule
  =  match vRHS (ctx,nwAs) vsb fcP xs
match vRHS (ctx,nwAs) vsb fcP (E (AbsTrm a s) (AbsTrm b t):xs)
  | a == b = match vRHS (ctx,nwAs) vsb fcP (anEConstr s t:xs)
  | otherwise = let fcP'= (aFConstr (AtmTrm a) t:fcP)
                    eqP = (anEConstr s (prmTrmApp [(a,b)] t):xs)
                in match vRHS (ctx,nwAs) vsb  fcP' eqP 
match vRHS (ctx,nwAs) vsb fcP (E (AppTrm f s) (AppTrm g t):xs) | f == g
  = match vRHS (ctx,nwAs) vsb fcP (anEConstr s t:xs)
match vRHS (ctx,nwAs) vsb fcP  (E (TplTrm s) (TplTrm  t):xs) | length s == length t
  = match vRHS (ctx,nwAs) vsb fcP (zipWith anEConstr s t ++ xs)
match vRHS (ctx,nwAs) vsb fcP (E v1@(VarTrm asb p x) v2@(VarTrm asb' p' y):xs) | x == y
  = fnD (match vRHS (ctx,nwAs) vsb fcP) diffSet
        where  atmSet  = S.union (atmActDom asb p) (atmActDom asb' p')
               diffSet = psi v1 v2 atmSet xs
match vRHS fc@(ctx,nwAs) vsb fcP (E s@(VarTrm asb p x) t:xs) | (not $ x `S.member` vRHS)
  = S.unions $ L.map (\(fc',s) -> match vRHS fc' vsb'@(vsbFn s) fcP (vsubProbApp fc' vsb' s)) caps' 
            where  atms = S.map anAtmTrm (aSbDom asb)
                   caps = cap atms t
                   caps' = S.toList $ S.map (aSbApp fc asb) caps
                   vsbFn = (\s -> M.insert x (prmTrmApp (prmInv p) s) vsb)
match _ _ _ _ (c:_) = S.empty --failure to match problem



--wrapper of frsh to return Ctxs
solveFrsh = toD . frsh


--freshness of an atm w/respect to a trmX (specialised to matching paper conference)
frsh :: Prob -> Set (Maybe Ctx)
frsh []
  = returnD (Just S.empty)
frsh ((F (AtmTrm a) (AtmTrm b)):xs)
  |a == b  = returnD Nothing
  |otherwise  = frsh xs
frsh ((F atm@(AtmTrm a) (AbsTrm b t)):xs)
  |a == b = frsh xs
  |otherwise = frsh ((F atm t):xs) 
frsh ((F a (AppTrm f t)):xs)
  = frsh ((F a t):xs) 
frsh ((F a (TplTrm t)):xs)
  = frsh ((map (aFConstr a) t) ++ xs)
frsh ((F atm@(AtmTrm a) var@(VarTrm asb p x)):xs)
  | M.null asb && L.null p = sqUnion (frsh xs) (returnD (Just (a,x)))
  | otherwise = let atmSet =  S.insert a $ aSbDom asb 
                    probs = psi atm var [] atmSet
                in S.unions toListD $ fnD (\p -> frsh (p ++ xs)) probs

                   
-- matching a given problem-in-context. Initial Sols to the matching problem must be filtered to discard potential pairs of form  (Set empty, Vsub), denoting failure.
--An initial set of new atoms with respect to the context and the problem has been added to deal with capture-avoidance substitution of abstraction terms.
--Aditionally, the given freshness context has been added to the problem as freshness constraints, therefore initially the freshness context passed to the function is empty, to be filled with primitive constraints of new atoms during the reduction of the matching problem.
solveMatch :: Ctx ->  Prob -> Sols
solveMatch ctx prob
    = let xs = varsRHSProb prob
          nwAtms = newAtms (atmsProbCtx ctx prob)
          ctxProb = ctx2Constr ctx
          result =  match xs (S.empty, nwAtms) M.empty ctxProb prob        
      in filterD (not . S.null . fst) result --preserve Sol where Ctxs is not empty
