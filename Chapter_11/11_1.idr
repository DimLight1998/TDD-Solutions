import Data.Primitives.Views

-- 1
every_other : Stream a -> Stream a
every_other (_ :: x :: xs) = x :: every_other xs

-- 2
data InfList : Type -> Type where
  (::) : (value: elem) -> Inf (InfList elem) -> InfList elem

implementation Functor InfList where
  map f (x :: xs) = f x :: map f xs

-- 3
randoms : Int -> Stream Int
randoms seed =
  let seed' = 1664525 * seed + 1013904223
   in (seed' `shiftR` 2) :: randoms seed'

data Face = Heads | Tails

getFace : Int -> Face
getFace n with (divides n 2)
  getFace ((2 * div) + rem) | (DivBy prf) = if rem == 0 then Heads else Tails

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips n s = take n (map getFace s)

-- 4
square_root_approx : (number : Double) -> (approx : Double) -> Stream Double
square_root_approx number approx =
  let next = (approx + (number / approx)) / 2
   in approx :: square_root_approx number next

square_root_bound : 
  (max : Nat)
  -> (number : Double)
  -> (bound : Double)
  -> (approxs: Stream Double)
  -> Double
square_root_bound Z number bound (a :: _) = a
square_root_bound (S k) number bound (a :: as) =
  if abs (a * a - number) < bound
    then a
    else square_root_bound k number bound as

square_root : (number : Double) -> Double
square_root number = square_root_bound 100 number 0.00000000001 (square_root_approx number number)
