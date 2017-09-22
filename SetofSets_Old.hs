module SetofSets where

import TrmX
import ConstraintsX
import qualified Data.List as L
import qualified Data.Map as Mp
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Maybe as M
import qualified Control.Applicative as A


-------------------------------------------------------------------------------
-- SET of sets ABSTRACT

-- constructs a singleton set of sets
returnD :: (Ord a, Eq a) => a -> Set a
returnD = S.singleton

--apply a function to elems of a set of sets
fnD ::(Ord a, Eq a, Ord b, Eq b) => (a ->  b) -> Set a -> Set b
fnD fn  = S.map fn -- fn must be defined concretely to b applied to sets

--filter out those sets s_i s.t. p(s_i)=False
filterD::(Ord a,Eq a) => (a -> Bool) -> Set a -> Set a
filterD p s = S.fromList [x | x <- S.elems s, p x]

--folder for set of sets  w initial element and function
foldrD::(Ord a, Eq a, Ord b, Eq b)=> (a -> b -> b) -> b -> S.Set a -> b
foldrD fn b = foldr fn b . S.elems

--convert sets to String
showSets :: (Ord a, Eq a, Show a) => (a -> String) -> S.Set a -> String
showSets fn s = "{ " ++ L.intercalate ",\n " (S.elems $ fnD fn s ) ++ " }"

------------------------Concrete types-----------------------
--union of sets of sets

--must find out if partial application (when Nothing) avoids solving to normal form next arg.
sqUnion:: Set (Maybe Ctx) -> Set (Maybe Ctx) -> Set (Maybe Ctx)
sqUnion d1 d2
   | hasNothingD d1 = d1
   | otherwise = S.fromList [S.union A.<$> ctx1 A.<*> ctx2 | ctx1 <- S.elems d1, ctx2 <- S.elems d2]

--strict left fold where empty is not allowed
sqUnions:: [S.Set (Maybe Ctx)]-> S.Set (Maybe Ctx)
sqUnions = L.foldl1' sqUnion

--atoms in sets of sets
atmsCtxs = foldrD (S.union . atmsCtx) S.empty 

--showCtxs
showCtxs = showSets showCtx

--remove inconsistencies (w.r.t. contexts)
rmInc:: S.Set (Maybe Ctx) -> S.Set (Maybe Ctx)
rmInc =filterD M.isJust

--convert to set of  Ctxs
toD:: S.Set (Maybe Ctx) -> Ctxs
toD s
    | S.null s'=  S.empty
    | otherwise=  fnD M.fromJust s'
    where s'=rmInc s

--convert to set of MAybe Ctxs
toMCtxs ctxs = if S.null ctxs then Nothing else Just ctxs

-- should have size 1 by default bc of applicative function sqUnion
hasEmptyD:: S.Set (Maybe Ctx) -> Bool
hasEmptyD s = S.size s == 1 && S.member (Just S.empty) s
              
hasNothingD:: S.Set (Maybe Ctx) -> Bool
hasNothingD s = S.size s == 1 && S.member Nothing s

-- context fc2 satisfies fc1
         --fc1    fc2
derives :: Ctx -> Ctxs -> Bool
derives fc ctxs =  any ( `S.isSubsetOf` fc) (S.elems ctxs)
