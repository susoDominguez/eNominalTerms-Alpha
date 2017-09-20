module ConstraintsX where

import TrmX
import qualified Data.List as L
import qualified Data.Map as Mp
import qualified Data.Set as S
--import qualified Data.Maybe as M
--import qualified Control.Applicative as A

--Data Structures

--A constraint
data Constr a =
  E {getL::a, getR:: a} | F {getL:: a, getR:: a} deriving (Show, Eq, Ord)

--constructors
anEConstr :: Trm -> Trm  -> Constr Trm
anEConstr  = E 

aFConstr :: Trm -> Trm -> Constr Trm
aFConstr  = F 

isEConstr :: Constr Trm -> Bool
isEConstr (E _ _) = True
isEConstr (F _ _) = False

--A list of Constraints
type Prob = [Constr Trm]--and then turn it into a list for input?
type ProbCtx = (Ctx,Prob)

--Vars and Atms in Prob
atmsConstr c =   (atmsTrm $ getR c) `S.union` (atmsTrm $ getL c)

atmsProb :: Prob ->S.Set Atm
atmsProb (c:prob)
  = atmsConstr c `S.union`  atmsProb prob
    
--common solution to all eq problems
type Sol= (VSub,  Ctxs)


-- Convert Fresh context into list of constraints
ctx2Constr :: Ctx -> Prob
ctx2Constr = map (\(a,t)-> (aFConstr (AtmTrm a) (VarTrm Mp.empty [] t))) . S.toList



--Functor
instance Functor Constr where
  fmap f (E s t) = E (f s) (f t)
  fmap f (F a t) = F (f a) (f t)

--single join of solutions
solUnion ::  Sol ->  Sol ->  Sol
solUnion (_,fc) (sb',fc') =  (sb',  fc `S.union` fc')


