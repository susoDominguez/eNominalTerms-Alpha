module Runner where

import Trm
import qualified Data.List as L
import qualified Data.Set as S
import Rewriting
import Alpha (solveAlpha)
import Constraints
import AuxFnRw (test)








runAlpha::  ProbCtx -> String
runAlpha (ctx, prob) = case solveAlpha prob of
                         Nothing -> "False"
                         Just fc -> if S.null fc || derives ctx fc then "True" else "True, when adding " ++ showCtx (S.difference fc ctx) ++ "\n"

runRw:: Rw -> TrmCtx -> [Rule] -> Either String (Ctx, [Trm])
runRw rw  trm@(fc,t) rls 
            | L.null msg = Right steps
            | otherwise = Left msg
            where msg=test t rls
                  steps= rewrites rw trm rls


                  
