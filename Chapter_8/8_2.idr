import Data.Vect

-- 1
myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl {x=m}
myPlusCommutes (S n') m = rewrite sym (plusSuccRightSucc m n') in cong (myPlusCommutes n' m)


-- 2
myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs where
  reverseNilProof : {n : Nat} -> Vect n a -> Vect (n + 0) a
  reverseNilProof {n} vect = rewrite plusZeroRightNeutral n in vect
  reverseConsProof : {n : Nat} -> {m : Nat} -> Vect (S (n + m)) a -> Vect (n + S m) a
  reverseConsProof {n} {m} vect = rewrite sym (plusSuccRightSucc n m) in vect
  reverse' : Vect n a -> Vect m a -> Vect (n + m) a
  reverse' acc [] = reverseNilProof acc
  reverse' acc (x :: xs) = reverseConsProof (reverse' (x :: acc) xs)
