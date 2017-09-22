--Atom substitution action
module Asb where

import TrmX
import ConstraintsX
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow

-------------------------------------------------------------------------
{-atom 2 term subst:   garbage collector on ID atm subs for each action-}

{- Composition of atm substitutions. The freshness context is used to derive fresh names
 when needed. -} 
aSbComp::Ctx -> Asb -> Asb -> Asb
aSbComp fc sb1 sb2 =
  let (frsh', sb1')  = M.mapAccum (\acc v -> aSbApp acc sb2 v) frsh sb1
      ks = M.keys sb1'
      (ctxs, trms)= unzip $ M.elems sb1'
      step3 k v = aSbFiltr . M.fromList $  zip k v
  in (frsh' ,S.unions ctxs  , step3 ks trms `M.union`  sb2) --union left-biased so it works
       

{-| Given an  atom 'a' and atom substitution \phi, it returns a-substitution \phi' where
   a\not\in\Dom(\phi'). -}
aSbDel:: Atm -> Asb -> Asb
aSbDel  = M.delete

-- application of atm subst to an atom, return atm itself as Trm if not found
aSbAtmApp:: Asb -> Atm -> Trm
aSbAtmApp sb a =  M.findWithDefault (anAtmTrm a) a sb


--application of atms subst to terms with generation of new names derived fromo given context
aSbApp:: Ctx -> Asb -> Trm  -> Trm
aSbApp _ sb  (AtmTrm a) =   aSbAtmApp sb a
aSbApp fc sb2 (VarTrm sb1 p x) =   let asb = aSbComp fc sb1 sb2
                                   in  aVarTrm asb p x
aSbApp fc sb abs@(AbsTrm a t)
   | a `M.member` asb =   aSbApp fc (aSbDel a sb) abs t--delete mapping [a-> Trm] from sb
   | otherwise =   AbsTrm newAtm trm
      where newAtm = frshen --TODO follow new definition
            trm = prmTrmApp [(newAtm, a)] t
aSbApp fc sb (AppTrm f t) = aSbApp fc sb t
aSbApp fc sb (TplTrm ts) = TplTrm ts'
   where ts' = L.map (aSbApp fc sb) ts
