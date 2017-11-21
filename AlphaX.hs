module AlphaX  (solveAlpha
               , isAlpha
               ) where

import TrmX
import TrmX_Actions
import ConstraintsX
import SetofSets
import Asb
import qualified Data.List as L
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import qualified Control.Monad as C
import qualified Control.Applicative as A
import Data.Maybe (isJust)



{- Derivability-}

--auxiliar fn for both frsh and eq; removes inconsistencies (=Nothing)
auxFn:: Var -> Atm -> ConstrX Trm -> Set (Maybe Ctx)
auxFn v a c
     | hasEmptyD nf = nf --if solvable by empty frshnss ctx, do not add disjunct a#x
     | hasNothingD nf = returnD (Just (aFC a v))--if inconsistent, add disjunct a#x
     | otherwise = S.union nf (returnD (Just (aFC a v))) --otherwise add both
   where nf = eq (c:[]) []

--iteration of auxFn applied to a set of atoms
freshFn atm asb p x  = 
   L.map (\c-> auxFn x (prmAtmApp (prmInv p) c) (aFConstr atm (aSbAtmApp asb c)))

diffSet asb p asb' p' x =
   L.map (\c-> auxFn x c (anEConstr (atmActAtm asb p c) (atmActAtm asb' p' c)))


--freshness of an atm w/respect to a trmX
frsh:: Prob -> Set (Maybe Ctx)
frsh []
  = returnD (Just S.empty)
frsh ((F (AtmTrm a) (AtmTrm b)):xs)|a==b
  = returnD Nothing
frsh ((F (AtmTrm a) (AtmTrm b)):xs)|a/=b
  = frsh xs
frsh ((F (AtmTrm a) (AbsTrm b t)):xs)|a==b
  = frsh xs
frsh ((F a (AbsTrm b t)):xs)
  = frsh ((F a t):xs) 
frsh ((F a (AppTrm f t)):xs)
  = frsh ((F a t):xs) 
frsh ((F a (TplTrm t)):xs)
  = frsh ((map (aFConstr a)t)++xs)
frsh ((F atm@(AtmTrm a) v@(VarTrm asb p x)):xs)
  =  sqUnions ((frsh xs) : freshFn' atmSet)
     where atmSet = S.singleton a `S.union` aSbDom asb 
           freshFn'= freshFn atm asb p x . toListD

-- alpha equality--first phase alpha, second phase frshness
eq :: Prob -> Prob -> Set (Maybe Ctx)
eq  acc [] 
  = frsh acc
eq  acc (f@(F a t):xs)  
  = eq  (f:acc)  xs  
eq   acc ((Eq (AtmTrm a) (AtmTrm b)):xs) | a == b
  = eq acc xs 
eq acc ((Eq (AbsTrm a s) (AbsTrm b t)):xs) | a==b
  =  eq  acc ((Eq s t):xs)
eq  acc ((Eq (AbsTrm a s) (AbsTrm b t)):xs) 
  = eq ((F (anAtmTrm b) s):acc) ((Eq (prmTrmApp [(a,b)] s) t):xs)
eq  acc  ((Eq (AppTrm f s) (AppTrm g t)):xs) | f==g
  =  eq acc ((Eq s t):xs)
eq  acc ((Eq (TplTrm s) (TplTrm  t)):xs) | length s == length t
  = eq acc ((map (\(si,ti)-> anEConstr si ti)  (zip s t))++xs)
eq  acc ((Eq (VarTrm asb p x) (VarTrm asb' p' y)):xs) | x==y
  = sqUnions ( (eq acc xs) : diffSet' atmSet)
     where atmSet  = S.union (atmActDom asb p) (atmActDom asb' p')
           diffSet' = diffSet  asb p asb' p' x . toListD 
eq _ (_:xs) = returnD Nothing

--function to solve derivability for a list of constraints. empty set is failure
solveAlpha:: Prob ->  Ctxs
solveAlpha = toD . (eq [])


--are trms alpha= by means of a (possibly empty) fc?
isAlpha:: Prob -> Bool
isAlpha = not . S.null . solveAlpha

