module AuxFnRwX where

import TrmX
import SetofSets
--import Constraints
--import Freshen
--import Matching (solveMatch)
import ClosednessX (genCtx,isClosed,closedness)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
--import qualified Data.Maybe as MB
--import qualified Control.Monad as C
--import qualified Control.Applicative as A
-----------------------CHECKS ON RULES N TERMS
--valid Rule
isValidRl :: Rule -> Bool
isValidRl (fc , l , r) = vars `S.isSubsetOf` varsTrm l
       where vars =  varsTrm r `S.union` varsCtx fc

isStandardRl :: Rule -> Bool
isStandardRl (fc, AppTrm _ _, r) = True
isStandardRl _ = False



validity ::  Rule -> String
validity rl@(fc,l,r) 
   |  not (isStandardRl rl) || not (isValidRl rl) =
      "Invalid Rule: " ++ showRule rl ++ ".\n"
   |  not $ isClosed (fc, TplTrm [l,r]) =
      "Rule Not Closed: "++showRule rl++
            case closedness (fc,TplTrm [l,r]) of
               Nothing ->"; unmatchable" ++ ".\n"
               Just ctxs ->"; add "++showSets showCtx ctxs++".\n"
   |  otherwise = []

------
ground t = if isGround t then [] else
              "Term " ++ showTrm t++ " must be ground." ++ "\n"


--positioning int
type Pos =  [Int]

------------------------------------------------
-- generate all subterms with positions for a term (trm)
subTrms :: Trm -> [(Pos, Trm)]
subTrms trm
       = let iter [] r = r
             iter (st @ (p, t) : ps) r = iter (ps ++ sub t) (st : r)
                where sub (AbsTrm _ t2) = [(0 : p, t2)]
                      sub (AppTrm _ t2) = [(0 : p, t2)]
                      sub (TplTrm ts) = zip (map (: p) [0..]) ts
                      sub _ = []
         in reverse (iter [([0], trm)] [])

-- replace a subterm at position (pos) in a term (trm1) with another term (trm2)
replaceTrmPos :: Pos -> Trm -> Trm -> Trm
replaceTrmPos pos trm1 trm2
    = let rplc p (AbsTrm a t1) = if p == pos then trm2 else AbsTrm a t1'
              where t1' = rplc (0 : p) t1
          rplc p (AppTrm s t1) = if p == pos then trm2 else AppTrm s t1'
              where t1' = rplc (0 : p) t1
          rplc p (TplTrm ts) = if p == pos then trm2 else TplTrm ts'
              where ts' = zipWith rplc  (map (: p) [0..]) ts
          rplc p t1 = if p == pos then trm2 else t1
      in rplc [0] trm1

-- search a term (trm) for a subterm at position (pos)
searchTrmPos :: Pos -> Trm -> Maybe Trm
searchTrmPos pos trm
    = let srch p t1 @ (AbsTrm _ t2)
              = if p == pos then Just t1 else srch (0 : p) t2
          srch p t1 @ (AppTrm _ t2)
              = if p == pos then Just t1 else srch (0 : p) t2
          srch p t1 @ (TplTrm ts)
              = if p == pos then Just t1 else iter (zip ts [0..])
              where iter [] = Nothing
                    iter ((s, n) : ps) = case srch (n : p) s of
                                             Nothing -> iter ps
                                             Just st -> Just st
          srch p t1 = if p == pos then Just t1 else Nothing
      in srch [0] trm
