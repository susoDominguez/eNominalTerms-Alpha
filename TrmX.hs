module TrmX where 

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow

-------------------------------------------------------------------------
{- DATA STRUCTURES -}

type Atm =  String --atoms
type Var =  String --unknowns
type Fun = String --term formers
type Ctx = S.Set (Atm,Var) --a context
type Ctxs = S.Set Ctx --list of contexts

data Trm = AtmTrm Atm  
         | VarTrm Asb Prm Var  --extended variable
         | AbsTrm Atm Trm
         | AppTrm Fun Trm
         | TplTrm [Trm] deriving (Eq, Ord)

--constructors
anAtmTrm:: Atm -> Trm
anAtmTrm  = AtmTrm 

aVarTrm:: Asb -> Prm -> Var -> Trm
aVarTrm  = VarTrm

anAbsTrm:: Atm -> Trm -> Trm
anAbsTrm = AbsTrm

anAppTrm:: Fun -> Trm -> Trm
anAppTrm = AppTrm

aFC:: Atm -> Var -> Ctx
aFC a v =  S.singleton (a,v)
------

type Prm = [(Atm, Atm)] --permutations
type Asb = M.Map Atm Trm --atom subs (simultaneous not sequential)
type VSub = M.Map Var Trm --var subs
type TrmCtx = (Ctx, Trm) --term-in-context

--to keep record of atoms: fst for existent atms, snd for available atoms
type FreshAtms = (S.Set Atm,S.Set Atm)

------------------------------------------------------------------------------------
{-Permutation actions-}

prmComp:: Prm -> Prm -> Prm --composition pi' circ pi => prmComp pi pi'
prmComp = (++)

prmInv :: Prm -> Prm --  pi^{-1}
prmInv = reverse

prmAtmApp :: Prm -> Atm -> Atm -- application to atoms
prmAtmApp [] a = a
prmAtmApp ((a,b): xs) n
   | n == a    = prmAtmApp xs b
   | n == b    = prmAtmApp xs a
   | otherwise = prmAtmApp xs n

--application to atm 2 term subs. pi is bijective so no clashes
prmAsbApp :: Prm -> Asb -> Asb 
prmAsbApp p asb = M.map (prmTrmApp p) $ M.mapKeys (prmAtmApp p) asb

prmTrmApp :: Prm -> Trm -> Trm -- application to terms
prmTrmApp p (AtmTrm a) = AtmTrm (prmAtmApp p a)
prmTrmApp p (AbsTrm a t) = AbsTrm (prmAtmApp p a) (prmTrmApp p t)
prmTrmApp p (VarTrm sb p' v) = VarTrm (prmAsbApp p sb) (prmComp p' p) v
prmTrmApp p (AppTrm f t) = AppTrm f (prmTrmApp p t)
prmTrmApp p (TplTrm xs) = TplTrm (map (prmTrmApp p) xs)

prmSupp :: Prm -> S.Set Atm --support of p => pi(a) /= a
prmSupp p = S.filter (\a -> prmAtmApp p a /= a) (atmsPrm p)

prmDs :: Prm -> Prm -> S.Set Atm -- difference set of prms: auxiliary function
prmDs p p' =  S.filter ds (prmSupp p `S.union` prmSupp p')
   where ds a = prmAtmApp p a /= prmAtmApp p' a
-------------------------------------------------------------------------------------------

-- Atom substitution

aSbFiltr :: Asb -> Asb -- filter out subs where a\in dom s.t. a = img(a)
aSbFiltr  = M.fromList . filter (uncurry f) . M.assocs
                 where f a t = anAtmTrm a /= t

aSbDom:: Asb -> S.Set Atm -- dom of atm subs, prior discard dom=img
aSbDom = M.keysSet . aSbFiltr

aSbImg:: Asb -> S.Set Trm --img of atm subs, prior discard dom=img
aSbImg = S.fromList . M.elems . aSbFiltr


--domain of both atom actions, pi and phi
atmActDom phi pi = aSbDom phi `S.union` prmSupp pi

-------------------------------------------------------------------------
--Context


-------------------------------------------------------------------------------
-- FRESHNESS CONTEXTS

ctxGen :: S.Set Atm -> S.Set Var -> Ctx
ctxGen atms vars
    = S.fromList [(a, v) | a <- S.elems atms, v <- S.elems vars]

-----------------
--groundTrm?
isGround  = S.null . varsTrm

------------------------------------------------------------------------------



{- RETURNING THE SET OF ATOMS & VARS-}


{- in freshness contexts -}
atmsCtx :: Ctx -> S.Set Atm
atmsCtx = S.map fst

varsCtx :: Ctx -> S.Set Var
varsCtx = S.map snd

atmsTrmCtx :: TrmCtx -> S.Set Atm
atmsTrmCtx (fc, t) = atmsCtx fc `S.union` atmsTrm t

varsTrmCtx :: TrmCtx -> S.Set Var
varsTrmCtx (fc, t) = varsCtx fc `S.union` varsTrm t


{-in atm 2 term subs-}
--both dom n Img
allAtmsAsb :: Asb -> S.Set Atm
allAtmsAsb asb
  =    M.keysSet asb `S.union` (S.unions . L.map atmsTrm $  M.elems asb)

varsAsb :: Asb -> S.Set Var
varsAsb =  S.unions . L.map varsTrm . M.elems

{-in unknown 2 term subs-}
atmsVSub :: VSub -> S.Set Atm
atmsVSub = S.unions . L.map atmsTrm . M.elems

varsVSub :: VSub -> S.Set Var
varsVSub  = S.unions . L.map varsTrm . M.elems 

{-in permutations-}
atmsPrm :: Prm -> S.Set Atm
atmsPrm = S.unions . map (\(a, b) -> S.fromList [a, b])

{-in  terms-} --all atoms including possible id perms\asbs
atmsTrm :: Trm -> S.Set Atm
atmsTrm (AtmTrm a) = S.singleton a
atmsTrm (AbsTrm a t) = S.insert a (atmsTrm t)
atmsTrm (VarTrm asb p _) = allAtmsAsb asb `S.union` atmsPrm p
atmsTrm (AppTrm f t) = atmsTrm t
atmsTrm (TplTrm xs) = S.unions $ map atmsTrm xs

varsTrm :: Trm -> S.Set Var
varsTrm (AtmTrm _) = S.empty
varsTrm (AbsTrm _ t) = varsTrm t
varsTrm (VarTrm asb _ v) = varsAsb asb `S.union` S.singleton v
varsTrm (AppTrm f t) = varsTrm t
varsTrm (TplTrm xs) = S.unions $ map varsTrm xs

{- in rules -}
atmsRl (fc,l,r) = atmsTrmCtx (fc, TplTrm [l,r])

varsRl (fc,l,r) = varsTrmCtx (fc, TplTrm [l,r])

{-RULES-}

--data structure
type Rule = (Ctx, Trm, Trm)

--------------------------------------------


---------------------------------------------------------------------------
{- PRETTY PRINTING-}

showPrm:: Prm -> String --permutations
showPrm [] = ""
showPrm ((a,b) : xs) = showPrm xs ++ "(" ++ a ++ " " ++  b ++ ")"

showCtx:: Ctx -> String -- freshness context
showCtx ctx = if S.null ctx
                 then "{}" 
                 else "{" ++ L.intercalate ", " (map (\(a,v) ->  a ++ "#" ++ v) (S.toList ctx)) ++ "}"

showTrm :: Trm -> String --terms
showTrm (AtmTrm a)       =  a
showTrm (VarTrm asb p v) = showAsb asb ++ (if null p || M.null asb then "" else "^" ) ++
                           showPrm p ++ (if null p && M.null asb then "" else "+") ++  v
showTrm (AbsTrm a t)     = "[" ++  a ++ "]" ++ " " ++ showTrm t
showTrm (AppTrm f t)     =  f ++ " " ++ showTrm t
showTrm (TplTrm [])     = ""
showTrm (TplTrm xs)     = "("++ L.intercalate ", " (map showTrm xs) ++ ")"


showAsb :: Asb -> String -- Atm 2 term fun
showAsb  =  M.foldrWithKey (\k t acc -> acc ++ f k t) ""
   where f k t = "[" ++  k ++ " -> " ++ showTrm t ++ "]"
         
showVSub:: VSub -> String
showVSub  = M.foldrWithKey (\k t acc -> acc ++ f k t) ""
   where f k t = "[" ++  k ++ " -> " ++ showTrm t ++ "]"

showTrmCtx:: TrmCtx -> String -- term-in-context
showTrmCtx (c, t) = showCtx c ++ " |- " ++ show t

instance Show Trm where show = showTrm
--instance Show Ctx where show = showCtx
--instance Show TrmCtx where show = showTrmCtx


showRule :: Rule -> String
showRule (fc,l,r) = showCtx fc ++ " |- " ++ showTrm l ++ " --> " ++ showTrm r


showSteps :: Ctx -> [Trm] -> String
showSteps fc ts = showCtx fc ++ " |- " ++ L.intercalate "-->" (map showTrm ts) ++ "." 
