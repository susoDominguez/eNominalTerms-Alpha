module ClosednessX where

import TrmX
import ConstraintsX
import MatchingX (solveMatch,solveMatch')
import SetofSets
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Freshen2
import qualified Control.Monad as C
import qualified Control.Applicative as A





isClosed:: TrmCtx -> Bool
isClosed s@(fc,t) = let (ctx',t')=freshenTFc s
                        a' = ctxGen (atmsTrm  t') (varsTrm t)
                        prob = anEConstr t' t:ctx2Constr fc
                     in case solveMatch  prob  of
                             Nothing -> False
                             Just (_,ctx) -> derives ( fc `S.union` a')  ctx

--find context needed for trm to be closed. Nothing means not matchable
closedness:: TrmCtx -> Maybe Ctxs
closedness s@(fc,t)
  = let (ctx',t')=freshenTFc s
        a' = ctxGen (atmsTrm  t') (varsTrm t)
        prob = anEConstr  t' t:ctx2Constr fc
    in case solveMatch  prob  of
        Nothing -> Nothing
        Just (_,ctx) -> Just (fnD (`S.difference` a') ctx)
