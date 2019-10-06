import Control.Monad.State

-- 1
update : (f : s -> s) -> State s ()
update f = get >>= \ x => put (f x)

-- 2
data Tree a = Empty | Node (Tree a) a (Tree a)

countEmpty : Tree a -> State Nat ()
countEmpty Empty = update S
countEmpty (Node x _ z) = countEmpty x >>= \ _ => countEmpty z

-- 3
countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update (\ (x, y) => (S x, y))
countEmptyNode (Node x _ z) = do
  countEmptyNode x
  (x, y) <- get
  put (x, S y)
  countEmptyNode z
