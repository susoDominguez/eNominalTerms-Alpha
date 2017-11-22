module TrmX_Actions where

                  {- Preamble -}
--containers
import Data.List
import qualified Data.List as L
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S

--exNomTrms
import TrmX


----------------------------Permutation actions


{-| Returns the composition of a pair of permutations, that is, given
  permutations p = (a b) and p = (a c)(d e), prmComp p p' = [(a c),(d e),(a b)]. -}
prmComp:: Prm -> Prm -> Prm
prmComp = (++)

{-| Returns the inverse of a permutation p, that is, p^{ -1}. -}
prmInv :: Prm -> Prm --  pi^{-1}
prmInv = reverse

--Application of a permutation to an atom symbol
prmAtmApp :: Prm -> Atm -> Atm
prmAtmApp [] a = a
prmAtmApp ((a,b): xs) n
   | n == a    = prmAtmApp xs b
   | n == b    = prmAtmApp xs a
   | otherwise = prmAtmApp xs n

{-Applies a permutation to set of atom substituion mappings,
 both to the set in the image and the set in the domain. -}
prmAsbApp :: Prm -> Asb -> Asb 
prmAsbApp p asb = aSbFiltr $ M.map (prmTrmApp p) $ M.mapKeys (prmAtmApp p) asb

{-| Applies a permutation to a Nominal term, resulting in the permuted Nominal
   term. -}
prmTrmApp :: Prm -> Trm -> Trm
prmTrmApp p (AtmTrm a)       = AtmTrm (prmAtmApp p a)
prmTrmApp p (AbsTrm a t)     = AbsTrm (prmAtmApp p a) (prmTrmApp p t)
prmTrmApp p (VarTrm sb p' v) = VarTrm (prmAsbApp p sb) (prmComp p' p) v
prmTrmApp p (AppTrm f t)     = AppTrm f (prmTrmApp p t)
prmTrmApp p (TplTrm xs)      = TplTrm (map (prmTrmApp p) xs)

{-| Returns the support of a permutation p, that is, {a|p(a)/=a, a::Atm}. -}
prmSupp :: Prm -> Set Atm
prmSupp p = S.filter (\a -> prmAtmApp p a /= a) (atmsPrm p)

{-| Returns the Difference Set between a pair of permutations, that is,
  for permutations p,p' and atom a, if p(a)=b and p'(a)=c, for any two distinct
  atoms b,c, then atom a is in their Difference set.-}
prmDs :: Prm -> Prm -> Set Atm
prmDs p p' =  S.filter ds (prmSupp p `S.union` prmSupp p')
   where ds a = prmAtmApp p a /= prmAtmApp p' a

         
-------------------------- Atom substitution actions

-- filter out identity atom subs from a given set of mappings
aSbFiltr :: Asb -> Asb 
aSbFiltr  = M.fromList . filter (uncurry f) . M.assocs
                 where f a t = anAtmTrm a /= t --keep only Asb where atom/=term

{-| Returns the domain of a set of Atom substitution mappings. -}
aSbDom:: Asb -> Set Atm
aSbDom = M.keysSet . aSbFiltr --filters out Id atm subs.

{-| Returns the image of a set of Atom substitution mappings. -}
aSbImg:: Asb -> Set Trm
aSbImg = S.fromList . M.elems . aSbFiltr --filters out Id atm subs


{-| Returns domain of both atom actions on a moderated variable,
 that is,  permutation and atm subs. -}
atmActDom phi pi = aSbDom phi `S.union` prmSupp pi


--------------------------- FRESHNESS CONTEXTS

{-| Given a set of atoms and a set of variable symbols, function ctxGen returns
 a freshness context, that is,  {a#X| a\in Set Atm, X\in Set Var -}
ctxGen :: Set Atm -> Set Var -> Ctx
ctxGen atms vars
    = S.fromList [(a, v) | a <- S.elems atms, v <- S.elems vars]



                 {- RETURNING THE SET OF ATOMS & VARS-}


{-| Set of atom symbols in a freshness context \Delta, that is,
  {a | a#X\in\Delta}. -}
atmsCtx :: Ctx -> Set Atm
atmsCtx = S.map fst

{-| Set of variable symbols in a freshness context \Delta, that is,
  {X | a#X\in\Delta}. -}
varsCtx :: Ctx -> Set Var
varsCtx = S.map snd

{-| Returns the set of atom symbols from a given Nominal term-in-Context. -}
atmsTrmCtx :: TrmCtx -> Set Atm
atmsTrmCtx (fc, t) = atmsCtx fc `S.union` atmsTrm t

{-| Returns the set of variable  symbols from a given Nominal term-in-Context. -}
varsTrmCtx :: TrmCtx -> Set Var
varsTrmCtx (fc, t) = varsCtx fc `S.union` varsTrm t

--returns set of all atoms in a set of atm subs mappings
allAtmsAsb :: Asb -> Set Atm
allAtmsAsb asb
    = aSbDom asb `S.union` (S.unions . L.map atmsTrm . M.elems $ aSbFiltr asb)

--returns set of variable symbols in a set of atm subs mappings
varsAsb :: Asb -> Set Var
varsAsb =  S.unions . L.map varsTrm . M.elems

{-Returns set of atms in a set of var subs mappings-}
atmsVSub :: VSub -> Set Atm
atmsVSub = S.unions . L.map atmsTrm . M.elems

{-Returns set of variable symbols in a set of var subs mappings-}
varsVSub :: VSub -> Set Var
varsVSub  = S.unions . L.map varsTrm . M.elems 

--returns all the names in a given permutation
atmsPrm :: Prm -> Set Atm
atmsPrm = S.unions . map (\(a, b) -> S.fromList [a, b])

{-| Returns the set of atom symbols from a given Nominal term. -}
atmsTrm :: Trm -> Set Atm
atmsTrm (AtmTrm a) = S.singleton a
atmsTrm (AbsTrm a t) = S.insert a (atmsTrm t)
atmsTrm (VarTrm asb p _) = allAtmsAsb asb `S.union` atmsPrm p
atmsTrm (AppTrm f t) = atmsTrm t
atmsTrm (TplTrm xs) = S.unions $ map atmsTrm xs

{-| Returns the set of UNABSTRACTED atom symbols from a given Nominal term. -}
atmsTrmF :: Trm -> Set Atm
atmsTrmF (AtmTrm a) = S.singleton a
atmsTrmF (AbsTrm a t) = atmsTrmF t
atmsTrmF (VarTrm asb p _) = allAtmsAsb asb `S.union` atmsPrm p
atmsTrmF (AppTrm f t) = atmsTrm t
atmsTrmF (TplTrm xs) = S.unions $ map atmsTrm xs

{-| Returns the set of variable symbols from a given Nominal term. -}
varsTrm :: Trm -> Set Var
varsTrm (AtmTrm _) = S.empty
varsTrm (AbsTrm _ t) = varsTrm t
varsTrm (VarTrm asb _ v) = varsAsb asb `S.union` S.singleton v
varsTrm (AppTrm f t) = varsTrm t
varsTrm (TplTrm xs) = S.unions $ map varsTrm xs

{-| returns a set of (fixed) new atoms with respect to another given set of atoms; the fixed set of potential new atoms ranges from a to z and from a0 to z9. -} 
newAtms :: Set Atm -> Set Atm
newAtms as =
  let atms = S.fromList $ [ (atm:show num) | atm <- ['a'..'z'], num <- [0..9]]
             ++ [(atm:[])| atm <- ['a'..'z']]
  in  S.difference atms as

{- Given a freshness context Ctx, a set of (new) atoms Set Atm and a set of variables xs, it returns a pair (a, (Ctx',Set Atm')) where Ctx' has a#X for each X in xs and Set Atm' is equalt to Set Atm except that it does not contain a. -}
freshen :: (Ctx, Set Atm) -> Set Var -> (Atm,CtxD)
freshen (ctx, nwAs) xs = (atm, (ctx `S.union` ctx', S.deleteAt 0 nwAs))
    where atm = S.elemAt 0 nwAs
          ctx' = ctxGen (S.singleton atm) xs

--------rewriting framework

{-| Returns the set of atoms existing in a nominal rewrite rule. -}
atmsRl (fc,l,r) = atmsTrmCtx (fc, TplTrm [l,r])

{-| Returns the set of variable symbols  existing in a nominal rewrite rule. -}
varsRl (fc,l,r) = varsTrmCtx (fc, TplTrm [l,r])

{-| Returns true when applied to a Nominal term containing
  no moderated variables. -}
isGround  = S.null . varsTrm
