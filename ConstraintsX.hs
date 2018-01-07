{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
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
data   ConstrX a   = E  {getL::a, getR::a} | F {getL::a, getR::a}

anEConstr :: Trm -> Trm  -> ConstrX Trm
anEConstr  = E 

aFConstr :: Trm -> Trm -> ConstrX Trm
aFConstr  = F

isEConstr:: ConstrX Trm -> Bool
isEConstr (E _ _) = True
isEConstr _ = False

instance Ord a => Ord (ConstrX a) where
   (E s t) `compare` (E s' t') =  let result = (s `compare` s')
                                    in if (result == EQ) then (t `compare` t') else result
   (F  a s) `compare` (F  a' s') =  let result = (a `compare` a')
                                    in if (result == EQ) then (s `compare` s') else result
   (E _ _) `compare` (F _ _) = GT
   (F _ _) `compare` (E _ _) = LT

instance Eq a => Eq (ConstrX a) where
   (E s t) == (E s' t') =  (s==s') && (t==t')
   (F  a s) == (F  a' s') =  (a==a') && (s==s')
   (E _ _) == (F _ _) = False
   (F _ _) == (E _ _) = False
   (E s t) /= (E s' t') =  not $ (E s t) == (E s' t')
   (F  a s) /= (F  a' s') =  not $ (F  a s) == (F  a' s')
   (E _ _) /= (F _ _)    =  True
   (F _ _) /= (E _ _)    =  True

instance Show a => Show (ConstrX a) where
   show (E s t) = show s ++ "=" ++ show t
   show (F a t) = show a ++ "#" ++ show t 

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

-- Convert freshness context into list of freshness constraints
ctx2Constr :: Ctx -> Prob
ctx2Constr = map (\(a,t)-> (aFConstr (anAtmTrm a) (aVarTrm M.empty [] t))) . S.toList


--solution  to a matching problem
type Sol  = (Ctxs, VSub)
type Sols = Set Sol

--pretty printing

showSol :: Sol -> String
showSol (ctxs, vsub) = "(" ++ showCtxs ctxs ++ ", " ++ showVSub vsub ++ ")"

showSols sols = "[" ++ L.intercalate ", " (map showSol $ S.toList sols) ++ "]"
