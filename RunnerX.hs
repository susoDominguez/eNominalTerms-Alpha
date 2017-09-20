module RunnerX where

import TrmX
import qualified Data.List as L
import qualified Data.Set as S
import RewritingX
import AlphaX (solveAlpha)
import ConstraintsX
import SetofSets
import AuxFnRwX









runAlpha::  ProbCtx -> String
runAlpha (ctx, prob) = case solveAlpha prob of
                          S.Set  Nothing -> "False"
                          fc -> if  derives ctx fc 
                                  then "True" 
                                     else "True, when adding " ++ showCtx (S.difference fc ctx) ++ "\n"

runRw:: Rw -> TrmCtx -> [Rule] -> Either String (Ctx, [Trm])
runRw rw  trm@(fc,t) rls 
            | L.null msg = Right steps
            | otherwise = Left msg
            where msg=test t rls
                  steps= rewrites rw trm rls

test :: Trm -> [Rule] -> String 
test t rls =foldr ((++) .  validity) rls ++ ground t
