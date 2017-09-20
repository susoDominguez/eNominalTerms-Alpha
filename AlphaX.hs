module AlphaX where

import TrmX
import ConstraintsX
import SetofSets
import Asb
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Control.Monad as C
import qualified Control.Applicative as A
import Data.Maybe (isJust)



{- Derivability-}

--auxiliar fn for both frsh and eq
auxFn:: Var -> Atm -> Constr Trm -> S.Set (Maybe Ctx)
auxFn v a c
     | hasEmptyD nf = nf
     | hasNothingD nf = returnD (Just (aFC a v))
     | otherwise = S.union nf (returnD (Just (aFC a v))) 
   where nf=eq [c]  []

--iteration of auxFn on problem
freshFn a asb p x  = 
   L.map (\b-> auxFn x (prmAtmApp (prmInv p) b) (aFConstr a (aSbAtmApp asb b)))

diffSet asb p asb' p' x =
   L.map (\a-> auxFn x a (anEConstr (atmActAtm asb p a) (atmActAtm asb' p' a)))


--freshness of an atm w/respect to a trmX
frsh:: Prob  -> S.Set (Maybe Ctx)
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
           freshFn'= freshFn atm asb p x . S.toList

-- alpha equality--first phase alpha, second phase frshness
eq :: Prob -> Prob -> S.Set (Maybe Ctx)
eq  acc [] 
  = frsh acc
eq  acc (f@(F a t):xs)  
  = eq  (f:acc)  xs  
eq   acc ((E (AtmTrm a) (AtmTrm b)):xs) | a == b
  = eq acc xs 
eq acc ((E (AbsTrm a s) (AbsTrm b t)):xs) | a==b
  =  eq  acc ((E s t):xs)
eq  acc ((E (AbsTrm a s) (AbsTrm b t)):xs) 
  = eq ((F (anAtmTrm b) s):acc) ((E (prmTrmApp [(a,b)] s) t):xs)
eq  acc  ((E (AppTrm f s) (AppTrm g t)):xs) | f==g
  =  eq acc ((E s t):xs)
eq  acc ((E (TplTrm s) (TplTrm  t)):xs) | length s == length t
  = eq acc ((map (\(si,ti)-> anEConstr si ti)  (zip s t))++xs)
eq  acc ((E (VarTrm asb p x) (VarTrm asb' p' y)):xs) | x==y
  = sqUnions ( (eq acc xs) : diffSet' atmSet)
    where diffSet' = diffSet  asb p asb' p' x . S.toList 
          atmSet  = S.union (atmActDom asb p) (atmActDom asb' p')
eq _ (_:xs) = returnD Nothing

-- function !$ keeps the size constant since it evaluates the construction of lists

--function to solve derivability for a list of constraints.empty set is failure
solveAlpha:: Prob ->  Ctxs
solveAlpha p = toD $  eq [] p


--are trms alpha= by means of a (possibly empty) fc?
isAlpha:: Prob -> Bool
isAlpha = not . S.null . solveAlpha

