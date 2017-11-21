--Atom substitution action
module Asb where

import TrmX
import ConstraintsX
import TrmX_Actions
import qualified Data.List as L
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Control.Arrow

-------------------------------------------------------------------------
{-atom 2 term subst:   garbage collector on ID atm subs for each action-}

{- Composition of atm substitutions. The freshness context is used to derive fresh names
 when needed. -} 
aSbComp::CtxD -> Asb -> Asb -> (CtxD,  Asb)
aSbComp fc sb1 sb2 =
  let (fc', sb1')  = M.mapAccum (\acc v -> aSbApp acc sb2 v) fc sb1
  in (fc', sb1' `M.union`  sb2) --union left-biased so it works
       

{-| Given an  atom 'a' and atom substitution \phi, it returns a-substitution \phi' where
   a\not\in\Dom(\phi'). -}
aSbDel:: Atm -> Asb -> Asb
aSbDel  = M.delete

-- application of atm subst to an atom, return atm itself as Trm if not found
aSbAtmApp:: Asb -> Atm -> Trm
aSbAtmApp sb a =  M.findWithDefault (anAtmTrm a) a sb


{-| Application of atm subst to terms with generation of new names derived fromo given context.-}
aSbApp:: CtxD -> Asb -> Trm  -> (CtxD, Trm)
aSbApp fc asb  (AtmTrm a) =   (fc,aSbAtmApp asb a)
aSbApp fc asb' (VarTrm asb p x)
  = let (fc',asb1) = aSbComp fc asb asb'
    in  (fc', aVarTrm asb1 p x)
aSbApp fc sb abs@(AbsTrm a t)
  =  (fc', AbsTrm nwAtm trm)
     where (nwAtm, fc') = freshen fc (varsTrm t)
           trm = prmTrmApp [(nwAtm, a)] t
aSbApp fc sb (AppTrm f t) = let (fc', trm) =  aSbApp fc sb t
                            in (fc', anAppTrm f trm)
aSbApp fc sb (TplTrm ts) = (fc', aTplTrm ts')
   where (fc', ts') = L.mapAccumL (\acc t-> aSbApp acc sb t) fc ts

{- application of permutation and atom substitution to an Atm. -}
atmActAtm :: Asb -> Prm -> Atm -> Trm
atmActAtm as prm = aSbAtmApp as . prmAtmApp prm
