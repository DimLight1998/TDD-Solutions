import Data.Primitives.Views
import System

%default total

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

Show GameState where
  show s = 
    show (correct (score s)) ++ "/" ++ show (attempted (score s)) ++ "\n" ++ "Difficulty: " ++ show (difficulty s)

initState : GameState
initState = MkGameState (MkScore 0 0) 12

addWrong : GameState -> GameState
addWrong = record { score -> attempted $= (+ 1) }

addCorrect : GameState -> GameState
addCorrect = record { score -> correct $= (+ 1)
                    , score -> attempted $= (+ 1)
                    }

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial forever : Fuel
forever = More forever

getRand : Int -> Int -> Int
getRand val max with (divides val max)
  getRand val 0 | DivByZero = 1
  getRand ((max * div) + rem) max | (DivBy prf) = abs rem + 1

runCommand : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand xs s (PutStr x) = putStr x >>= \ _ => pure ((), xs, s)
runCommand xs s GetLine = getLine >>= \ str => pure (str, xs, s)
runCommand xs s GetRandom = pure (getRand (head xs) (difficulty s), tail xs, s)
runCommand xs s GetGameState = pure (s, xs, s)
runCommand xs s (PutGameState x) = pure ((), xs, x)
runCommand xs s (Pure x) = pure (x, xs, s)
runCommand xs s (Bind x f) = runCommand xs s x >>= \ (v, xs', s') => runCommand xs' s' (f v)

run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run Dry xs s consoleIO = pure (Nothing, xs, s)
run (More x) xs s (Quit y) = pure (Just y, xs, s)
run (More x) xs s (Do z f) = runCommand xs s z >>= \ (v, xs', s') => run x xs' s' (f v)

randoms : Int -> Stream Int
randoms seed =
  let seed' = 1663526 * seed + 1013904223
   in (seed' `shiftR` 2) :: randoms seed'

data Input = Answer Int | QuitCmd

readInput : (prompt : String) -> Command Input
readInput prompt = do
  PutStr prompt
  answer <- GetLine
  if toLower answer == "quit"
    then Pure QuitCmd
    else Pure (Answer (cast answer))

-- 1
updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = GetGameState >>= \ s => PutGameState (f s)

-- 2
Functor Command where
  map f command = Bind command (\ v => Pure (f v))

Applicative Command where
  pure = Pure
  x <*> y = Bind x (\ xv => Bind y (\ yv => Pure (xv yv)))

Monad Command where
  (>>=) = CommandDo.(>>=)
-- end of 2

mutual
  correct : ConsoleIO GameState
  correct = do
    PutStr "Correct!\n"
    updateGameState addCorrect
    quiz

  wrong : Int -> ConsoleIO GameState
  wrong ans = do
    PutStr ("Wrong, the answer is " ++ show ans ++ "\n")
    updateGameState addWrong
    quiz

  quiz : ConsoleIO GameState
  quiz = do
    num1 <- GetRandom
    num2 <- GetRandom
    s <- GetGameState
    PutStr (show s ++ "\n")
    input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
    case input of
      Answer answer =>
        if answer == num1 * num2
          then correct
          else wrong (num1 * num2)
      QuitCmd => Quit s

partial
main : IO ()
main = do
  seed <- time
  (Just score, _, state) <- run forever (randoms (fromInteger seed)) initState quiz
  putStrLn ("Final score: " ++ show state)

-- 3
record Votes where
  constructor MkVotes
  upvotes : Integer
  downvotes : Integer

record Article where
  constructor MkArticle
  title : String
  url : String
  score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

getScore : Article -> Integer
getScore a = upvotes (score a) - downvotes (score a)

addUpvote : Article -> Article
addUpvote = record { score -> upvotes $= (+ 1) }

addDownvote : Article -> Article
addDownvote = record { score -> downvotes $= (+ 1) }
