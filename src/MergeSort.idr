module MergeSort
import Data.List.Views as V

%hide merge
%hide sort
%default total

lteOrGte : (x, y : Nat) -> Either (LTE x y) (GTE x y)
lteOrGte Z _ = Left LTEZero
lteOrGte _ Z = Right LTEZero
lteOrGte (S k) (S j) with (lteOrGte k j)
    | (Left ltekj) = Left (LTESucc ltekj) 
    | (Right gtekj) = Right (LTESucc gtekj)

notLTE : Not (LTE x y) -> LTE y x
notLTE {x = x} {y = y} contra with (lteOrGte x y) 
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

allLTEtrans : LTE x y -> All (LTE y) ys -> All (LTE x) ys
allLTEtrans _ AllNil = AllNil
allLTEtrans ltexy (AllCons py allys) = 
    AllCons (lteTransitive ltexy py) (allLTEtrans ltexy allys)
    
allAppend : All p xs -> All p ys -> All p (xs ++ ys)
allAppend AllNil pa = pa
allAppend (AllCons px allx) ally = 
    AllCons px (allAppend allx ally)

allPerm : All p xs -> Permutation xs ys -> All p ys
allPerm _ PermNil = AllNil
allPerm (AllCons p1 all) (PermCons p2) = AllCons p1 (allPerm all p2)
allPerm (AllCons p1 (AllCons p2 all)) PermSwap = (AllCons p2 (AllCons p1 all))
allPerm allxs (PermTrans p1 p2) = allPerm (allPerm allxs p1) p2
    
data Ordered : List Nat -> Type where
    OrdNil : Ordered []
    OrdCons : Ordered xs -> All (\x => y `LTE` x) xs -> Ordered (y::xs)

orderedSingle : Ordered [x]
orderedSingle = OrdCons OrdNil AllNil

mergeLemma : All (LTE x) xs -> All (LTE y) ys -> LTE x y -> Permutation (xs ++ y::ys) zs ->
     All (LTE x) zs
mergeLemma xsltex ysltey ltexy p =
    let ysltex = allLTEtrans ltexy ysltey in
    let yssltex = AllCons ltexy ysltex in
    allPerm (allAppend xsltex yssltex) p

merge : (xs : List Nat) -> Ordered xs -> (ys : List Nat) -> Ordered ys -> 
    (zs : List Nat ** (Ordered zs, Permutation (xs ++ ys) zs))
merge [] _ ys ordys = 
    (ys ** (ordys, permRefl))
merge xs ordxs [] _ = 
    rewrite appendNilRightNeutral xs in
    (xs ** (ordxs, permRefl))
merge (x::xs) (OrdCons ordxs p1) (y::ys) (OrdCons ordys p2) with (isLTE x y)
    | Yes ltexy =
        let (zs ** (ordzs, permzs)) = (merge xs ordxs (y::ys) (OrdCons ordys p2)) in
        let ordxzs = OrdCons ordzs (mergeLemma p1 p2 ltexy permzs) in
        (x::zs ** (ordxzs, PermCons permzs)) 
    | No contra = 
        let (zs ** (ordzs, permzs)) = merge (x::xs) (OrdCons ordxs p1) ys ordys in
        let ordyzs = OrdCons ordzs (mergeLemma p2 p1 (notLTE contra) (PermTrans permAppComm permzs)) in
        let tmp = PermCons (PermTrans permAppComm permzs) in
        let permyzs = PermTrans (permAppComm {xs = (x::xs)}) tmp in
        (y::zs ** (ordyzs, permyzs))

mergeSortLemma : Permutation xs1 xs -> Permutation ys1 ys -> 
    Permutation (xs ++ ys) zs -> Permutation (xs1 ++ ys1) zs
mergeSortLemma p1 p2 p = 
    PermTrans (permAppFront p2) (PermTrans (permAppBack p1) p)

mergeSort : (xs : List Nat) -> (ys : List Nat ** (Ordered ys, Permutation xs ys))
mergeSort xs with (V.splitRec xs)
    mergeSort [] | SplitRecNil = ([] ** (OrdNil, permRefl))
    mergeSort [x] | SplitRecOne = ([x] ** (orderedSingle, permRefl))
    mergeSort (ys ++ zs) | SplitRecPair ysrec zsrec = 
        let (rs1 ** (ordrs1, permrs1)) = (mergeSort ys | ysrec) in
        let (rs2 ** (ordrs2, permrs2)) = (mergeSort zs | zsrec) in 
        let (rs ** (ordrs, permrs)) = merge rs1 ordrs1 rs2 ordrs2 in
        (rs ** (ordrs, mergeSortLemma permrs1 permrs2 permrs))
