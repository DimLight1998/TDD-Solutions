-- 1
data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

total takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z [] = Exact []
takeN (S k) [] = Fewer
takeN Z xxs = Exact []
takeN (S k) (x :: xs) = case takeN k xs of
  Fewer => Fewer {xs = x :: xs}
  Exact ys {rest = rest} => Exact (x :: ys) {rest = rest}

-- test
groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

-- 2
halves : List a -> (List a, List a)
halves xs with (takeN ((length xs) `div` 2) xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)
