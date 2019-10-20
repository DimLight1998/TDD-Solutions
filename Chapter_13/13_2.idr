import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () h (S h)
  Pop : StackCmd Integer (S h) h
  Top : StackCmd Integer (S h) (S h)

  Pure : a -> StackCmd a h h
  (>>=) : StackCmd a h1 h2 -> (a -> StackCmd b h2 h3) -> StackCmd b h1 h3

  GetStr : StackCmd String h h
  PutStr : String -> StackCmd () h h

runStack : Vect n Integer -> StackCmd a n n' -> IO (a, Vect n' Integer)
runStack vec (Push x) = pure ((), x :: vec)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)
runStack vec (Pure x) = pure (x, vec)
runStack vec (x >>= f) = do
   (out, vec') <- runStack vec x
   runStack vec' (f out)
runStack vec GetStr = do
  line <- getLine
  pure (line, vec)
runStack vec (PutStr str) = do
  putStr str
  pure ((), vec)

data StackIO : Nat -> Type where
  Do : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1

namespace StackIO
  (>>=) : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial forever : Fuel
forever = More forever

run : Fuel -> Vect h Integer -> StackIO h -> IO ()
run Dry vec sio = pure ()
run (More x) vec (Do y f) = do
  (out, vec') <- runStack vec y
  run x vec' (f out)

-- user commands

data StkInput
  = Number Integer
  | Add
  | Sub
  | Mult
  | Neg
  | Discard
  | Dup

doAdd : StackCmd () (S (S h)) (S h)
doAdd = do
  a <- Pop
  b <- Pop
  Push (a + b)

doSub : StackCmd () (S (S h)) (S h)
doSub = do
  a <- Pop
  b <- Pop
  Push (b - a)

doMult : StackCmd () (S (S h)) (S h)
doMult = do
  a <- Pop
  b <- Pop
  Push (a * b)

doNeg : StackCmd () (S h) (S h)
doNeg = do
  a <- Pop
  Push (-a)

doDiscard : StackCmd Integer (S h) h
doDiscard = Pop

doDup : StackCmd Integer (S h) (S (S h))
doDup = do
  a <- Top
  Push a
  Pure a

strToInput : String -> Maybe StkInput
strToInput "" = Nothing
strToInput "add" = Just Add
strToInput "subtract" = Just Sub
strToInput "multiply" = Just Mult
strToInput "negate" = Just Neg
strToInput "discard" = Just Discard
strToInput "duplicate" = Just Dup
strToInput x =
  if all isDigit (unpack x)
    then Just (Number (cast x))
    else Nothing

mutual
  tryAdd : StackIO h
  tryAdd {h = (S (S _))} = do
    doAdd
    x <- Top
    PutStr $ (show x) ++ "\n"
    stackCalc
  tryAdd = do
    PutStr "invalid"
    stackCalc

  trySub : StackIO h
  trySub {h = (S (S _))} = do
    doSub
    x <- Top
    PutStr $ (show x) ++ "\n"
    stackCalc
  trySub = do
    PutStr "invalid"
    stackCalc

  tryMult : StackIO h
  tryMult {h = (S (S _))} = do
    doMult
    x <- Top
    PutStr $ (show x) ++ "\n"
    stackCalc
  tryMult = do
    PutStr "invalid"
    stackCalc

  tryNeg : StackIO h
  tryNeg {h = S _} = do
    doNeg
    x <- Top
    PutStr $ (show x) ++ "\n"
    stackCalc
  tryNeg = do
    PutStr "invalid"
    stackCalc

  tryDiscard : StackIO h
  tryDiscard {h = S _} = do
    x <- doDiscard
    PutStr $ "discarded " ++ (show x) ++ "\n"
    stackCalc
  tryDiscard = do
    PutStr "invalid"
    stackCalc

  tryDup : StackIO h
  tryDup {h = S _} = do
    doDup
    x <- Top
    PutStr $ "duplicated " ++ (show x) ++ "\n"
    stackCalc
  tryDup = do
    PutStr "invalid"
    stackCalc

  stackCalc : StackIO h
  stackCalc = do
    PutStr "> "
    input <- GetStr
    case strToInput input of
      Nothing => do
        PutStr "invalid input"
        stackCalc
      (Just (Number x)) => do
        Push x
        stackCalc
      (Just Add) => tryAdd
      (Just Sub) => trySub
      (Just Mult) => tryMult
      (Just Neg) => tryNeg
      (Just Discard) => tryDiscard
      (Just Dup) => tryDup

main : IO ()
main = run forever [] stackCalc
