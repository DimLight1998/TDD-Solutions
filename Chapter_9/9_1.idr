-- 1
data Elem : a -> List a -> Type where
  Here : Elem x (x :: ys)
  There : Elem x xs -> Elem x (y :: ys)

-- 2
data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

Uninhabited (Last [] x) where
  uninhabited LastOne impossible
  uninhabited (LastCons _) impossible

onlyOneNotEq : DecEq a => {x : a} -> {y : a} -> (x = y -> Void) -> Last [x] y -> Void
onlyOneNotEq notEq LastOne = notEq Refl
onlyOneNotEq _ (LastCons _) impossible

lastNotEq :
  DecEq a
  => {x : a} -> {y : a} -> {xs : List a}
  -> (xs = [] -> Void) -> (Last xs y -> Void) -> Last (x :: xs) y -> Void
lastNotEq nonEmpty lastNeq LastOne = nonEmpty Refl
lastNotEq nonEmpty lastNeq (LastCons prf) = lastNeq prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] y = No absurd
isLast (x :: xs) y = case decEq xs [] of
  Yes Refl => case decEq x y of
    Yes Refl => Yes LastOne
    No neq => No (onlyOneNotEq neq)
  No nonEmpty => case isLast xs y of
    Yes prf => Yes (LastCons prf)
    No notLast => No (lastNotEq nonEmpty notLast)
