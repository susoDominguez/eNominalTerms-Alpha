module ConstraintsX(
   ConstrX(..)
  ,anEConstr, aFConstr, isEqConstr
  , Prob, ProbCtx
  , atmsProb, varsProb
  , Sol, Sols
  , ctx2Constr) where

import TrmX
import TrmX_Actions
import qualified Data.List as L
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
--import qualified Data.Maybe as M
--import qualified Control.Applicative as A

--Data Structure
data   ConstrX a   = Eq  {getL::a, getR::a} | F {getL::a, getR::a}

anEConstr :: Trm -> Trm  -> ConstrX Trm
anEConstr  = Eq 

aFConstr :: Trm -> Trm -> ConstrX Trm
aFConstr  = F

isEqConstr:: ConstrX Trm -> Bool
isEqConstr (Eq _ _) = True
isEqConstr _ = False

instance Eq a => Eq (ConstrX a) where
   (Eq s t) == (Eq s' t') =  (s==s') && (t==t')
   (F  a s) == (F  a' s') =  (a==a') && (s==s')
   (Eq s t) /= (Eq s' t') =  not $ (Eq s t) == (Eq s' t')
   (F  a s) /= (F  a' s') =  not $ (F  a s) == (F  a' s')
   (Eq _ _) /= (F _ _)    =  True


--A list of Constraints
type Prob = [ConstrX Trm]--and then turn it into a list for input?
type ProbCtx = (Ctxs,Prob)

--atms in a constraint
atmsConstr c =   (atmsTrm $ getR c) `S.union` (atmsTrm $ getL c)

--atoms in a problem
atmsProb :: Prob -> Set Atm
atmsProb []        = S.empty
atmsProb (c:prob)  = atmsConstr c `S.union`  atmsProb prob

--Var symbols in a constraint
varsConstr c =   (varsTrm $ getR c) `S.union` (varsTrm $ getL c)

--Var symbols in a problem
varsProb :: Prob -> Set Var
varsProb []        = S.empty
varsProb (c:prob)  = varsConstr c `S.union`  varsProb prob
    
--solution  to a matching problem
type Sol  = (Ctxs, VSub)
type Sols = Set Sol


-- Convert Fresh context into list of constraints
ctx2Constr :: Ctx -> Prob
ctx2Constr = map (\(a,t)-> (aFConstr (anAtmTrm a) (aVarTrm M.empty [] t))) . S.toList


--single join of solutions
-- solUnion ::  Sol ->  Sol ->  Sol
-- solUnion (_,fc) (sb',fc') =  (sb',  fc `S.union` fc')


