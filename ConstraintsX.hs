module ConstraintsX where

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

instance Ord a => Ord (ConstrX a) where
   (Eq s t) `compare` (Eq s' t') =  if ((s `compare` s') == EQ) then (t `compare` t') else EQ
   (F  a s) `compare` (F  a' s') =  if ((a `compare` a') == EQ) then (s `compare` s') else EQ

instance Eq a => Eq (ConstrX a) where
   (Eq s t) == (Eq s' t') =  (s==s') && (t==t')
   (F  a s) == (F  a' s') =  (a==a') && (s==s')
   (Eq s t) /= (Eq s' t') =  not $ (Eq s t) == (Eq s' t')
   (F  a s) /= (F  a' s') =  not $ (F  a s) == (F  a' s')
   (Eq _ _) /= (F _ _)    =  True


--A list of Constraints
type Prob = [ConstrX Trm]

--atms in a constraint
atmsConstr c =  (atmsTrm $ getL c) `S.union` (atmsTrm $ getR c)

--atoms in a problem
atmsProb :: Prob -> Set Atm
atmsProb []        = S.empty
atmsProb (c:prob)  = atmsConstr c `S.union`  atmsProb prob

--atoms in a problem-in-context
atmsProbCtx :: Ctx -> Prob -> Set Atm
atmsProbCtx ctx p = (atmsCtx ctx) `S.union` (atmsProb p)

--Var symbols in a constraint
varsConstr c = (varsTrm $ getL c) `S.union` (varsTrm $ getR c)

--Var symbols in a problem
varsProb :: Prob -> Set Var
varsProb []        = S.empty
varsProb (c:prob)  = varsConstr c `S.union`  varsProb prob

--Var symbols in RHS of a  problem
varsRHSProb :: Prob -> Set Var
varsRHSProb []        = S.empty
varsRHSProb (c:prob)  = (varsTrm $ getR c) `S.union`  varsProb prob
    
--solution  to a matching problem
type Sol  = (Ctxs, VSub)
type Sols = Set Sol

-- Convert freshness context into list of freshness constraints
ctx2Constr :: Ctx -> Prob
ctx2Constr = map (\(a,t)-> (aFConstr (anAtmTrm a) (aVarTrm M.empty [] t))) . S.toList

