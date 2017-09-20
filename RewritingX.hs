module RewritingX where

import TrmX
import ConstraintsX
import Freshen
import MatchingX (solveMatch,solveMatch')
import ClosednessX (genCtx)
import Asb (vsubApp)
import SetofSets (derives)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
--import qualified Data.Maybe as MB
import qualified Control.Monad as C
import qualified Control.Applicative as A
import AuxFnRwX

--types of rewriting
data Rw = NR | ClNR | NRout | ClNRout  deriving (Show,Eq,Read)

isNR NR = True
isNR _ = False


isNRout NRout = True
isNRout _ = False

areNRs rw = isNR rw || isNRout rw

isClNR ClNR = True
isClNR _ = False

isClNRout ClNRout = True
isClNRout _ = False

areClNRs rw =  isClNR rw || isClNRout rw


-------------------------------------------------------------------------------
-----------------STANDARD & CLOSED REWRITING  FOR CLOSED TERMS:

--IMPORTANT: standard rules must start with an AppTrm. Ground terms only

--(am i using FreshAtms?)
----find 1st matching position in a rule. generalised but must be for ground terms
findMatch::  FreshAtms -> Ctx -> [(Pos,Trm)] -> TrmCtx -> Maybe (Pos, VSub)
findMatch _  _ [] t = Nothing
findMatch fAtms fc ((pos,t):xs) (ctx,l)
  = case solveMatch (anEConstr l t:ctx2Constr ctx) of
     Nothing -> findMatch fAtms fc xs (ctx,l)
     Just (sigma,fc2)-> if derives fc fc2 
                        then Just (pos,sigma)
                        else Nothing --else findMatch ctx xs (fc,l) -}


--one rewrite step, when no match in rule is reflexive step
aStep:: Rw -> TrmCtx -> Rule -> TrmCtx
aStep rw  trm@(fc,t) rl@(ctx,l,r)
  = let (ctx',l',r') = freshenVars rl t
        posT = if isNR rw  then subTrms t else reverse $ subTrms t
        fn a b= S.union (atmsCtx a)  (atmsTrmCtx b)
    in case findMatch (fn fc (ctx',l'),S.empty) fc posT (ctx',l') of
        Nothing -> trm
        Just (pos,vsub)-> let (atms,(fctx,instR'))= vsubApp (fn fc  (ctx',TplTrm [r',t]),S.empty) vsub r'
                          in ( fc `S.union` fctx, replaceTrmPos pos t  instR')

--one closed rewrite step
aStepC:: Rw -> TrmCtx -> Rule -> TrmCtx
aStepC rw  trm@(fc,t) rl@(ctx, l,r)
  = let (ctx',l',r') = freshenRnT rl trm
        posT = if isClNR rw then subTrms t else reverse $ subTrms t
        fc' = S.union fc (genCtx (atmsTrm l') (varsTrmCtx (fc,t)) )
        fn a b= S.union (atmsCtx a)  (atmsTrmCtx b)  
    in case findMatch (fn fc' (ctx',l'),S.empty) fc' posT (ctx',l') of
        Nothing -> trm
        Just (pos,vsub) -> let (atms,(fctx,instR'))= vsubApp (fn fc'  (ctx',TplTrm [r',t]),S.empty) vsub r'
                           in ( fc' `S.union` fctx, replaceTrmPos pos t  instR')

--leftmost innermost many rewrites. First set of rules must be empty at init. reverse results
manyStep:: [Rule] -> Rw -> TrmCtx -> [Rule] -> [TrmCtx]
manyStep _ _  _ [] = [] --when no rule matches, ends
manyStep rl1 rw  trm@(ctx,t) rl2@(r:rs)
             | areClNRs rw &&  t/= snd stepC = stepC:resetRl stepC
             | areNRs rw &&  t/= snd step = step:resetRl step
             | otherwise = nextRule
     where step=aStep rw trm r --ctx1 should b same across rewrites
           stepC=aStepC rw trm r --add original ctx to ctxC when printing
           resetRl st= manyStep [] rw st (reverse rl1 ++ rl2)
           nextRule = manyStep (r:rl1) rw trm rs



--rewriting function. checking constraints bf passing rules n terms to here
rewrites :: Rw ->  TrmCtx -> [Rule] ->(Ctx, [Trm])
rewrites rw  trm@(ctx,t) rl = let (ctxs , ts) = unzip $  manyStep [] rw  trm rl
                                 in (S.unions (ctx:ctxs), t: ts)

