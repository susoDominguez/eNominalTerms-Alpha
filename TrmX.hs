--Syntax of Nominal Terms extended with atom substitutions
module TrmX
       (
         )
where 

----------------PREAMBLE

--containers
import qualified Data.List as L
import Data.Map(Map)
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S

--base
import Control.Arrow

------------------------------------ DATA STRUCTURES

--Type aliases for nominal structures
type Atm  = String --type of atom symbol
type Var  = String --type of variable symbol
type Fun  = String --type of term formers
type Ctx  = Set (Atm,Var) --type of freshness context
type Ctxs = Set Ctx --type of collection of contexts

--type aliases for permutations and substitutions
type Prm    = [(Atm, Atm)] --type of permutations: list of atom swappings
type Asb    = Map Atm Trm --type of atom substitutions
type VSub   = Map Var Trm --type of variable substitutions
type TrmCtx = (Ctx, Trm) --type of terms-in-context

--to keep record of atoms: fst for atms in system, snd for available atoms
type FreshAtms = (S.Set Atm,S.Set Atm)

{-| Nominal terms with primitive atom substituion can be:
   Atom terms, Moderated variables where the permutations are suspended first
   and then the atom substitutions, Abstraction terms, Function applications and
   Tuple terms.-}
data Trm = AtmTrm Atm  
         | VarTrm Asb Prm Var
         | AbsTrm Atm Trm
         | AppTrm Fun Trm
         | TplTrm [Trm] deriving (Eq, Ord)

--Nominal term constructors
anAtmTrm:: Atm -> Trm
anAtmTrm  = AtmTrm 

aVarTrm:: Asb -> Prm -> Var -> Trm
aVarTrm  = VarTrm

anAbsTrm:: Atm -> Trm -> Trm
anAbsTrm = AbsTrm

anAppTrm:: Fun -> Trm -> Trm
anAppTrm = AppTrm

aTplTrm:: [Trm] -> Trm
aTplTrm = TplTrm

--freshness context constructor
aFC:: Atm -> Var -> Ctx
aFC a v =  S.singleton (a,v)




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
prmAsbApp p asb = M.map (prmTrmApp p) $ M.mapKeys (prmAtmApp p) asb

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
prmDs :: Prm -> Prm -> S.Set Atm
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

--returns set of atoms in a set of atm subs mappings
allAtmsAsb :: Asb -> Set Atm
allAtmsAsb asb
  =    M.keysSet asb' `S.union` (S.unions . L.map atmsTrm $ M.elems asb')
       where asb' = aSbFiltr asb

--returns set of variable symbols in a set of atm subs mappings
varsAsb :: Asb -> Set Var
varsAsb =  S.unions . L.map varsTrm . M.elems

{-Returns set of atms in a set of var subs mappings-}
atmsVSub :: VSub -> S.Set Atm
atmsVSub = S.unions . L.map atmsTrm . M.elems

{-Returns set of variable symbols in a set of var subs mappings-}
varsVSub :: VSub -> S.Set Var
varsVSub  = S.unions . L.map varsTrm . M.elems 

--returns all the names in a given permutation
atmsPrm :: Prm -> S.Set Atm
atmsPrm = S.unions . map (\(a, b) -> S.fromList [a, b])

{-| Returns the set of atom symbols from a given Nominal term. -}
atmsTrm :: Trm -> S.Set Atm
atmsTrm (AtmTrm a) = S.singleton a
atmsTrm (AbsTrm a t) = S.insert a (atmsTrm t)
atmsTrm (VarTrm asb p _) = allAtmsAsb asb `S.union` atmsPrm p
atmsTrm (AppTrm f t) = atmsTrm t
atmsTrm (TplTrm xs) = S.unions $ map atmsTrm xs

{-| Returns the set of variable symbols from a given Nominal term. -}
varsTrm :: Trm -> S.Set Var
varsTrm (AtmTrm _) = S.empty
varsTrm (AbsTrm _ t) = varsTrm t
varsTrm (VarTrm asb _ v) = varsAsb asb `S.union` S.singleton v
varsTrm (AppTrm f t) = varsTrm t
varsTrm (TplTrm xs) = S.unions $ map varsTrm xs

{-| Returns the set of atoms existing in a nominal rewrite rule. -}
atmsRl (fc,l,r) = atmsTrmCtx (fc, TplTrm [l,r])

{-| Returns the set of variable symbols  existing in a nominal rewrite rule. -}
varsRl (fc,l,r) = varsTrmCtx (fc, TplTrm [l,r])

{-| Returns true when applied to a Nominal term containing
  no moderated variables. -}
isGround  = S.null . varsTrm


{-RULES-}

--data structure
type Rule = (Ctx, Trm, Trm)

--------------------------------------------


---------------------------------------------------------------------------
{- PRETTY PRINTING-}

--printing permutations
showPrm:: Prm -> String
showPrm [] = ""
showPrm ((a, b) : xs)| a==b = showPrm xs --discards Identity swaps
showPrm ((a,b) : xs) = showPrm xs ++ "(" ++ a ++ " " ++  b ++ ")"

--printing a freshness context
showCtx:: Ctx -> String
showCtx ctx =
  if S.null ctx
     then "{}"
           else "{" ++ L.intercalate ", " (map (\(a,v) ->  a ++ "#" ++ v) (S.toList ctx)) ++ "}"

--printing a nominal term
showTrm :: Trm -> String
showTrm (AtmTrm a)       =  a
showTrm (VarTrm asb p v) = showAsb asb ++ (if null p || M.null asb then "" else "^" ) ++
                           showPrm p ++ (if null p && M.null asb then "" else "+") ++  v
showTrm (AbsTrm a t)     = "[" ++  a ++ "]" ++ " " ++ showTrm t
showTrm (AppTrm f t)     =  f ++ " " ++ showTrm t
showTrm (TplTrm [])     = ""
showTrm (TplTrm xs)     = "("++ L.intercalate ", " (map showTrm xs) ++ ")"

--print atom subs
showAsb :: Asb -> String
showAsb  =  M.foldrWithKey (\k t acc -> acc ++ f k t) ""
   where f k t = "[" ++  k ++ " -> " ++ showTrm t ++ "]"

--prints a set of variable mappings
showVSub:: VSub -> String
showVSub  = M.foldrWithKey (\k t acc -> acc ++ f k t) ""
   where f k t = "[" ++  k ++ " -> " ++ showTrm t ++ "]"

--prints a term-in-context
showTrmCtx:: TrmCtx -> String
showTrmCtx (c, t) = showCtx c ++ " |- " ++ show t

instance Show Trm where show = showTrm
--instance Show Ctx where show = showCtx
--instance Show TrmCtx where show = showTrmCtx

--prints a nominal rewrite rule
showRule :: Rule -> String
showRule (fc,l,r) = showCtx fc ++ " |- " ++ showTrm l ++ " --> " ++ showTrm r

--prints a sequence of nominal reduction steps
showSteps :: Ctx -> [Trm] -> String
showSteps fc ts = showCtx fc ++ " |- " ++ L.intercalate "-->" (map showTrm ts) ++ "." 
