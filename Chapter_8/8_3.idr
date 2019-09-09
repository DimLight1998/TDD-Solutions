data Vect : Nat -> Type -> Type where
  Nil : Vect 0 a
  (::) : a -> Vect k a -> Vect (S k) a

-- 1
headUnequal : DecEq a =>
  {xs : Vect n a}
  -> {ys : Vect n a}
  -> (contra : (x = y) -> Void)
  -> ((x :: xs) = (y :: ys))
  -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a =>
  {xs : Vect n a}
  -> {ys : Vect n a}
  -> (contra : (xs = ys) -> Void)
  -> ((x :: xs) = (y :: ys))
  -> Void
tailUnequal contra Refl = contra Refl

-- 2
aux : {xs : Vect k a} -> {ys : Vect k a} -> (x = y) -> (xs = ys) -> (x :: xs = y :: ys)
aux Refl Refl = Refl

DecEq a => DecEq (Vect k a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case (decEq x y, decEq xs ys) of
    (Yes prfHead, Yes prfTail) => Yes (aux prfHead prfTail)
    (No contraHead, _) => No (headUnequal contraHead)
    (_, No contraTail) => No (tailUnequal contraTail)
