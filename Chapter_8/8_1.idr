-- 1
same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons = cong

-- 2
same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists (Refl {x=x}) = same_cons {x=x}

-- 3
data ThreeEq : a -> b -> c -> Type where
  ThreeRefl : ThreeEq x x x

-- 4
allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS _ _ _ (ThreeRefl {x=k}) = ThreeRefl {x=S k}
