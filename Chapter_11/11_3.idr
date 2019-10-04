import System
import Data.Primitives.Views

%default total

namespace Command
  data Command : Type -> Type where
    PutStr : (str : String) -> Command ()
    GetLine : Command String
    ReadFile : (filepath : String) -> Command (Either FileError String)
    WriteFile : (filepath : String) -> (content : String) -> Command (Either FileError ())
    Pure : (val : ty) -> Command ty
    Bind : (x : Command a) -> (f : a -> Command b) -> Command b

  (>>=) : (x : Command a) -> (f : a -> Command b) -> Command b
  (>>=) = Bind

runCommand : Command a -> IO a
runCommand (PutStr str) = putStr str
runCommand GetLine = getLine
runCommand (ReadFile filepath) = readFile filepath
runCommand (WriteFile filepath content) = writeFile filepath content
runCommand (Pure val) = pure val
runCommand (Bind x f) = runCommand x >>= \ y => runCommand (f y)

namespace ConsoleIO
  data ConsoleIO : Type -> Type where
    Quit : (ret : t) -> ConsoleIO t
    Do : (cmd : Command a) -> (cont : a -> Inf (ConsoleIO b)) -> ConsoleIO b

  (>>=) : (cmd : Command a) -> (cont : a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel : Type where
  Dry : Fuel
  More : (more : Lazy Fuel) -> Fuel

partial forever : Fuel
forever = More forever

run : (fuel : Fuel) -> (consoleIO : ConsoleIO a) -> IO (Maybe a)
run Dry _ = pure Nothing
run (More more) (Quit ret) = pure (Just ret)
run (More more) (Do cmd cont) = runCommand cmd >>= (\ x => run more (cont x))

quiz : (s : Stream Int) -> (score : Nat) -> (ques : Nat) -> ConsoleIO (Nat, Nat)
quiz (num1 :: num2 :: nums) score ques = do
  PutStr ("Score so far: " ++ show score ++ " / " ++ show ques ++ "\n")
  PutStr (show num1 ++ " * " ++ show num2 ++ "? ")
  answer <- GetLine
  if toLower answer == "quit"
    then Quit (score, ques)
    else
      if (cast answer == num1 * num2)
        then do
          PutStr "Correct!\n"
          quiz nums (score + 1) (ques + 1)
        else do
          PutStr ("Wrong, the answer is: " ++ show (num1 * num2) ++ "\n")
          quiz nums score (ques + 1)

randoms : Int -> Stream Int
randoms seed =
  let seed' = 1664525 * seed + 1013904223
   in (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

-- 1 run ":exec main_1" in repl
partial main_1 : IO ()
main_1 = do
  seed <- time
  Just (score, ques) <- run forever (quiz (arithInputs (fromInteger seed)) 0 0)
  putStrLn ("Final score: " ++ show score ++ " / " ++ show ques)

-- 2 & 3
shell : ConsoleIO String
shell = do
  line <- GetLine
  let slices = split (== ' ') line
  case slices of
    "cat" :: filename :: [] => do
      res <- ReadFile filename
      case res of
        Left _ => Quit "Read Error"
        Right content => PutStr content >>= (\ _ => shell)
    "copy" :: source :: destination :: [] => do
      res1 <- ReadFile source
      case res1 of
        Left _ => Quit "Read Error"
        Right content => do
          res2 <- WriteFile destination content
          case res2 of
            Left _ => Quit "Write Error"
            Right _ => shell
    "exit" :: [] => Quit "Exit"
    _ => Quit "Parse Error"

partial main_2 : IO ()
main_2 = do
  Just res <- run forever shell
  putStrLn res
