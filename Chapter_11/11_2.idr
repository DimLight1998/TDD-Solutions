-- 1
data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

run : (fuel : Fuel) -> (actions : InfIO) -> IO ()
run Dry _ = pure ()
run (More fuel) (Do action cont) = action >>= (\ x => run fuel (cont x))

totalREPL : (prompt : String) -> (action : String -> String) -> InfIO
totalREPL prompt action = do
  putStr prompt
  input <- getLine
  putStr (action input)
  totalREPL prompt action
