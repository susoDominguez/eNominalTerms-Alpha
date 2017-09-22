module ConstraintsX where

import TrmX
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
--import qualified Data.Maybe as M
--import qualified Control.Applicative as A

--Data Structures

--A constraint class
class (Functor a) => Constraint a where
     getL:: a -> Trm
     getR:: a -> Trm
     isEqConstr?:: a -> Bool

--constructors
instance Constraint Constr where
   getL (_ s _) = s
   getR (_ _ t) = t
   isEqConstr? (E _ _) = True
   isEqConstr? _       = False
   fmap f (E s t) = E (f s) (f t)
   fmap f (F a t) = F   a   (f t)


--data structures
data Constr = E Trm Trm | F Trm Trm

anEConstr :: Trm -> Trm  -> Constr
anEConstr  = E 

aFConstr :: Trm -> Trm -> Constr
aFConstr  = F 


--A list of Constraints
type Prob = [Constr]--and then turn it into a list for input?
type ProbCtx = (Ctx,Prob)

--Vars and Atms in Prob
atmsConstr c =   (atmsTrm $ getR c) `S.union` (atmsTrm $ getL c)

atmsProb :: Prob -> Set Atm
atmsProb (c:prob)
  = atmsConstr c `S.union`  atmsProb prob
    
--common solution to all eq problems
type Sol= (Ctxs, Vsub)


-- Convert Fresh context into list of constraints
ctx2Constr :: Ctx -> Prob
ctx2Constr = map (\(a,t)-> (aFConstr (AtmTrm a) (VarTrm Mp.empty [] t))) . S.toList


--single join of solutions
solUnion ::  Sol ->  Sol ->  Sol
solUnion (_,fc) (sb',fc') =  (sb',  fc `S.union` fc')


