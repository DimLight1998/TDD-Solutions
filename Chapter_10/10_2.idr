import Data.Vect
import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views

-- 1
total equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys with (snocList xs)
  equalSuffix [] ys | Empty = []
  equalSuffix (zs ++ [x]) ys | Snoc xsRec with (snocList ys)
    equalSuffix (zs ++ [x]) [] | Snoc xsRec | Empty = []
    equalSuffix (zs ++ [x]) (ws ++ [y]) | Snoc xsRec | Snoc ysRec =
      if x == y
        then (equalSuffix zs ws | xsRec | ysRec) ++ [x]
        else []

-- 2
total mergeSort : Ord a => Vect n a -> Vect n a
mergeSort vs with (splitRec vs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (xs ++ ys) | (SplitRecPair lrec rrec) = merge (mergeSort xs | lrec) (mergeSort ys | rrec)

-- 3
total toBinary : Nat -> String
toBinary Z = "0"
toBinary n with (halfRec n)
  toBinary Z | HalfRecZ = ""
  toBinary (x + x) | (HalfRecEven rec) = toBinary x | rec ++ "0"
  toBinary (S (x + x)) | (HalfRecOdd rec) = toBinary x | rec ++ "1"

-- 4
total palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec) = (x == y) && (palindrome ys | rec)
