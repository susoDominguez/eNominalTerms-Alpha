---------------------------Vsub app
module VarSubApp where

import TrmX
import TrmX_Actions
import ConstraintsX
import AlphaX
import Asb
import SetofSets
import qualified Data.List as L
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

--Variable substitution application with respect to Matching. It may need a different approach when used in rewriting framework

{-| vsbSearch looks for a particular variable instance returning Just Trm or Nothing otherwise.-}
vsbSearch :: Var -> VSub -> Maybe Trm
vsbSearch  = M.lookup

{-| action of Var Subs on a Term. A freshness context and a set of new atmos is given to the function to deal with atom substitution applications. -}
vsubApp :: CtxD -> VSub -> Trm -> (CtxD, Trm)
vsubApp fc vsb t@(VarTrm asb p x)
  = case vsbSearch x vsb of
     Nothing -> (fc,t)
     Just s  -> atmActionsTrm fc' asb' p s
       where (fc', asb') = vsubAppAsb fc vsb asb
vsubApp fc vsb (AppTrm f t)
  = (fc', anAppTrm f trm)
   where (fc', trm) = vsubApp fc vsb t
vsubApp fc vsb (TplTrm ts)
  = (fc', aTplTrm ts')
  where (fc',ts') = L.mapAccumL (\acc t-> vsubApp acc vsb t) fc ts
vsubApp fc vsb (AbsTrm a t)
  = (fc', anAbsTrm a trm)
    where (fc', trm) = vsubApp fc vsb t 
vsubApp fc _ t = (fc,t)

--v substitution applied to atm substitutions
vsubAppAsb ctx vsb asb = M.mapAccum (\acc elem -> vsubApp acc vsb elem) ctx asb

-- idempotent substitution composition: see baader & snyder
vsubComp :: CtxD -> VSub -> VSub -> (CtxD, VSub)
vsubComp fc sb1 sb2
 = (fc' , sb1' `M.union`  sb2)
    where (fc', sb1') = M.mapAccum (\acc t -> vsubApp acc sb2 t) fc sb1

          
--apply both perm and asubs to a term
atmActionsTrm fc asb p = aSbApp fc asb . prmTrmApp p

--vsubApp for ConstrX data structure. Adapted for matching, so only applies to RHS term
vsubCnApp:: CtxD -> VSub -> ConstrX Trm -> (CtxD, ConstrX Trm)
vsubCnApp fc vsb c
     | isEConstr c = (fc' $ getL c, E (trm $ getL c) (getR c))
     | otherwise = (fc' $ getR c, F (getL c) (trm $ getR c))
     where fn = vsubApp fc vsb
           trm = (snd . fn)
           fc' = (fst . fn)


--vsubApp for a problem, requires 2 functions. vsb2Constr is the main one
vsubProbApp fc vsb prob = L.mapAccumL (\acc p -> vsubCnApp acc vsb p) fc prob
