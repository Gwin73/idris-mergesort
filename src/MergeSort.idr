module MergeSort
import Data.List.Views as V

%hide merge
%hide sort
%default total

interface DecEq a => DecTotOrd a where
    lte : a -> a -> Type
    total decLTE : (x : a) -> (y : a) -> Dec (x `lte` y)
    total antiSym : x `lte` y -> y `lte` x -> x = y
    total trans : x `lte` y -> y `lte` z -> x `lte` z
    total connex : (x, y : a) -> Either (x `lte` y) (y `lte` x)

notLTE : DecTotOrd a => {x, y : a} -> Not (lte x y) -> lte y x
notLTE {x = x} {y = y} contra with (connex x y) 
    | (Left ltexy) = absurd (contra ltexy)
    | (Right gtexy) = gtexy

data Permutation : List a -> List a -> Type where
    PermNil : Permutation [] []
    PermCons : Permutation xs xs' -> Permutation (x::xs) (x::xs')
    PermSwap : Permutation (y::x::xs) (x::y::xs)
    PermTrans : Permutation xs ys -> Permutation ys zs -> Permutation xs zs

permRefl : Permutation xs xs
permRefl {xs = []} = PermNil
permRefl {xs = x :: xs} = 
    PermCons (permRefl {xs = xs})

permSym : Permutation xs ys -> Permutation ys xs
permSym PermNil = PermNil
permSym (PermCons p) = PermCons (permSym p)
permSym PermSwap = PermSwap
permSym (PermTrans p1 p2) = PermTrans (permSym p2) (permSym p1)

permAppFront : Permutation xs xs' -> Permutation (ys ++ xs) (ys ++ xs')
permAppFront {ys = []} p = p
permAppFront {ys = (y :: ys)} p = 
    PermCons (permAppFront p)

permAppBack : Permutation xs xs' -> Permutation (xs ++ ys) (xs' ++ ys)
permAppBack PermNil = permRefl
permAppBack (PermCons p) = PermCons (permAppBack p)
permAppBack PermSwap = PermSwap
permAppBack (PermTrans p1 p2) = 
    let ih1 = permAppBack p1 in 
    let ih2 = permAppBack p2 in
    PermTrans ih1 ih2

permAppComm : Permutation (xs ++ ys) (ys ++ xs)
permAppComm {xs = []} {ys = ys} = 
    rewrite appendNilRightNeutral ys in 
    permRefl
permAppComm {xs = (x :: xs)} {ys = []} = 
    rewrite appendNilRightNeutral (x :: xs) in 
    permRefl
permAppComm {xs = (x :: xs)} {ys = (y :: ys)} = 
    let ih1 = permAppComm {xs = xs} {ys = ys} in 
    let ih2 = permAppComm {xs = (x::xs)} {ys = ys} in 
    let ih3 = permAppComm {xs = xs} {ys = (y::ys)} in
    PermTrans 
        (PermCons (PermTrans ih3 (PermCons (permSym ih1))))
        (PermTrans PermSwap (PermCons ih2))

data All : (a -> Type) -> List a -> Type where
    AllNil : All p []
    AllCons : p x -> All p xs -> All p (x::xs)

allLTEtrans : DecTotOrd a => {x, y : a} -> {ys : List a} -> lte x y -> All (lte y) ys -> All (lte x) ys
allLTEtrans _ AllNil = AllNil
allLTEtrans {x = x} ltexy (AllCons py allys) = 
    AllCons (trans {x = x} ltexy py) (allLTEtrans ltexy allys)

allAppend : DecTotOrd a => {xs, ys : List a} -> All p xs -> All p ys -> All p (xs ++ ys)
allAppend AllNil pa = pa
allAppend (AllCons px allx) ally = 
    AllCons px (allAppend allx ally)
 
allPerm : DecTotOrd a => {xs, ys : List a} -> All p xs -> Permutation xs ys -> All p ys
allPerm _ PermNil = AllNil
allPerm (AllCons p1 all) (PermCons p2) = AllCons p1 (allPerm all p2)
allPerm (AllCons p1 (AllCons p2 all)) PermSwap = (AllCons p2 (AllCons p1 all))
allPerm allxs (PermTrans p1 p2) = allPerm (allPerm allxs p1) p2
 
data Ordered : List a -> Type where
    OrdNil : Ordered []
    OrdCons : DecTotOrd a => {xs : List a} -> {y : a} -> Ordered xs -> All (\x => y `lte` x) xs -> Ordered (y::xs)

orderedSingle : DecTotOrd a => {x : a} -> Ordered [x]
orderedSingle = OrdCons OrdNil AllNil

mergeLemma : DecTotOrd a => {x, y : a} -> {xs, ys, zs : List a} -> All (lte x) xs -> All (lte y) ys -> lte x y -> Permutation (xs ++ y::ys) zs ->
        All (lte x) zs
mergeLemma xsltex ysltey ltexy p =
    let ysltex = allLTEtrans ltexy ysltey in
    let yssltex = AllCons ltexy ysltex in
    allPerm (allAppend xsltex yssltex) p

merge : DecTotOrd a => (xs : List a) -> Ordered xs -> (ys : List a) -> Ordered ys -> 
    (zs : List a ** (Ordered zs, Permutation (xs ++ ys) zs))
merge [] _ ys ordys = 
    (ys ** (ordys, permRefl))
merge xs ordxs [] _ = 
    rewrite appendNilRightNeutral xs in
    (xs ** (ordxs, permRefl))
merge (x::xs) (OrdCons ordxs p1) (y::ys) (OrdCons ordys p2) with (decLTE x y)
    | Yes ltexy =
        let (zs ** (ordzs, permzs)) = (merge xs ordxs (y::ys) (OrdCons ordys p2)) in
        let ordxzs = OrdCons ordzs (mergeLemma ?u1 p2 ltexy permzs) in -- ?u1 should be p1 but causes contraint mismatch
        (x::zs ** (ordxzs, PermCons permzs))  
    | No contra = 
        let (zs ** (ordzs, permzs)) = merge (x::xs) (OrdCons ordxs ?u2) ys ordys in -- ?u2 should be p1 but causes contraint mismatch
        let lteyx = notLTE {x = x} contra in
        let tmp1 = PermTrans (permAppComm {xs = ys}) permzs in
        let ordyzs = OrdCons ordzs (mergeLemma p2 ?u3 lteyx tmp1) in -- ?u3 should be p1 but causes contraint mismatch
        let tmp2 = (PermCons (PermTrans (permAppComm {xs = ys}) permzs)) in
        let permyzs = PermTrans (permAppComm {xs = (x::xs)}) tmp2 in
        (y::zs ** (ordyzs, permyzs))
        
mergeSortLemma : DecTotOrd a => {xs1, xs, ys1, ys, zs : List a} -> Permutation xs1 xs -> Permutation ys1 ys -> 
    Permutation (xs ++ ys) zs -> Permutation (xs1 ++ ys1) zs
mergeSortLemma p1 p2 p = 
    PermTrans (permAppFront p2) (PermTrans (permAppBack p1) p)

mergeSort : DecTotOrd a => (xs : List a) -> (ys : List a ** (Ordered ys, Permutation xs ys))
mergeSort xs with (V.splitRec xs)
    mergeSort [] | SplitRecNil = ([] ** (OrdNil, permRefl))
    mergeSort [x] | SplitRecOne = ([x] ** (orderedSingle, permRefl))
    mergeSort (ys ++ zs) | SplitRecPair ysrec zsrec = 
        let (rs1 ** (ordrs1, permrs1)) = (mergeSort ys | ysrec) in
        let (rs2 ** (ordrs2, permrs2)) = (mergeSort zs | zsrec) in 
        let (rs ** (ordrs, permrs)) = merge rs1 ordrs1 rs2 ordrs2 in
        (rs ** (ordrs, mergeSortLemma permrs1 permrs2 permrs))
