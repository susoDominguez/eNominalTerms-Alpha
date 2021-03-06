module SetofSets where

import TrmX
import ConstraintsX
import qualified Data.List as L
import qualified Data.Map as Mp
import Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Maybe as M
import qualified Control.Applicative as A


-------------------------------------------------------------------------------
-- SET of sets ABSTRACT

-- constructs a singleton set of sets
returnD :: (Ord a, Eq a) => a -> Set a
returnD = S.singleton

--apply a function to elems of a set of sets
fnD ::(Ord a, Eq a, Ord b, Eq b) => (a -> b) -> Set a -> Set b
fnD fn  = S.map fn -- fn must be defined concretely to b applied to sets

--filter out those sets s_i s.t. p(s_i)=False
filterD ::(Ord a,Eq a) => (a -> Bool) -> Set a -> Set a
filterD p s = S.fromList [x | x <- S.elems s, p x]

--folder for set of sets  w initial element and function
foldrD::(Ord a, Eq a, Ord b, Eq b)=> (a -> b -> b) -> b -> Set a -> b
foldrD fn b = foldr fn b . S.elems

--convert set to list
toListD :: (Ord a, Eq a) => Set a -> [a]
toListD = S.toList

--convert sets to String
showSets :: (Ord a, Eq a, Show a) => (a -> String) -> Set a -> String
showSets fn s = "{ " ++ L.intercalate ",\n " (S.elems $ fnD fn s ) ++ " }"

------------------------Concrete types-----------------------
--union of sets of sets

--must find out if partial application (when Nothing) avoids solving to normal form next arg.
sqUnion:: Set (Maybe Ctx) -> Set (Maybe Ctx) -> Set (Maybe Ctx)
sqUnion d1 d2
  = S.fromList [S.union A.<$> ctx1 A.<*> ctx2 | ctx1 <- S.elems d1, ctx2 <- S.elems d2]

--strict left fold where empty is not allowed
sqUnions:: [Set (Maybe Ctx)]-> Set (Maybe Ctx)
sqUnions = L.foldl1' sqUnion

--showCtxs
showCtxs = showSets showCtx

--remove inconsistencies (w.r.t. contexts)
rmInc:: Set (Maybe Ctx) -> Set (Maybe Ctx)
rmInc =filterD M.isJust

--convert to set of  Ctxs
toD:: Set (Maybe Ctx) -> Ctxs
toD s
    | S.null s' =  S.empty
    | otherwise =  fnD M.fromJust s'
    where s' = rmInc s

-- A singleton of empty freshness context
hasEmptyD:: S.Set (Maybe Ctx) -> Bool
hasEmptyD s = S.size s == 1 && S.member (Just S.empty) s

--A singleton of Nothing
hasNothingD:: S.Set (Maybe Ctx) -> Bool
hasNothingD s = S.size s == 1 && S.member Nothing s

--any context of Ctxs satisfies a given ctx
derives :: Ctx -> Ctxs -> Bool
derives ctx ctxs =  any (\e -> e `S.isSubsetOf` ctx) (S.elems ctxs)
