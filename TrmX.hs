--Syntax of Nominal Terms extended with atom substitutions
module TrmX
       (Trm(..)
        , FreshAtms
        , Rule
        , Prm
        , Atm
        , Var
        , Fun
        , Ctx
        , Ctxs
        , Asb
        , VSub
        , TrmCtx
        , anAtmTrm
        , aVarTrm
        , anAbsTrm
        , anAppTrm
        , aTplTrm
        , aTrmCtx
        , aFC
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
--import Control.Arrow

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
type FreshAtms = (Set Atm,Set Atm)

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

--term-in-context constructor
aTrmCtx :: Ctx -> Trm -> TrmCtx
aTrmCtx = (\x y -> (x,y))

--freshness context constructor
aFC:: Atm -> Var -> Ctx
aFC a v =  S.singleton (a,v)

{-RULES-}

{- | An extended nominal rewrite rule consists of a freshness context \Delta,
   a left term t and a right term s. It is denoted as \Delta |- t -> s and
   represented as type (Ctx, Trm, Trm) where Ctx is the type of \Delta and Trm
   is the type of both terms t,s. Term t is placed in the middle position and
   s in the last position. -}
type Rule = (Ctx, Trm, Trm)

------------------------------{- PRETTY PRINTING-}

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
showTrm (VarTrm asb p v) = showAsb asb ++ (if null p || M.null asb then "" else "^" )                           ++ showPrm p ++ (if null p && M.null asb then "" else "+") ++ v
showTrm (AbsTrm a t)     = "[" ++  a ++ "]" ++ " " ++ showTrm t
showTrm (AppTrm f t)     =  f ++ " " ++ showTrm t
showTrm (TplTrm [])      = ""
showTrm (TplTrm xs)      = "("++ L.intercalate ", " (map showTrm xs) ++ ")"

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
