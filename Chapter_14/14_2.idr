-- 1
namespace _1
  data Access = LoggedOut | LoggedIn
  data PwdCheck = Correct | Incorrect

  data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
    Password : String -> ShellCmd PwdCheck LoggedOut (\ s => case s of
      Correct => LoggedIn
      Incorrect => LoggedOut
    )
    Logout : ShellCmd () LoggedIn (const LoggedOut)
    GetSecret : ShellCmd String LoggedIn (const LoggedIn)
    PutStr : String -> ShellCmd () state (const state)
    Pure : (res : ty) -> ShellCmd ty (stateFn res) stateFn
    (>>=) : ShellCmd a state1 state2Fn
            -> ((res : a) -> ShellCmd b (state2Fn res) state3Fn)
            -> ShellCmd b state1 state3Fn


-- 2
namespace _2
  VendState : Type
  VendState = (Nat, Nat)

  data Input = COIN | VEND | CHANGE | REFILL Nat
  data CoinResult = OK | Rejected

  data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
    InsertCoin : MachineCmd CoinResult (pounds, chocs)
      (\ coinResult => case coinResult of
        OK => (S pounds, chocs)
        Rejected => (pounds, chocs)
      )
    Vend : MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
    GetCoins : MachineCmd () (pounds, chocs) (const (Z, chocs))
    Refill : (bars : Nat) -> MachineCmd () (Z, chocs) (const (Z, bars + chocs))
    Display : String -> MachineCmd () state (const state)
    GetInput : MachineCmd (Maybe Input) state (const state)
    Pure : (res : ty) -> MachineCmd ty (fn res) fn
    (>>=) : MachineCmd a state1 state2Fn
            -> ((res : a) -> MachineCmd b (state2Fn res) state3Fn)
            -> MachineCmd b state1 state3Fn

  data MachineIO : VendState -> Type where
    Do : MachineCmd a state1 state2Fn
         -> ((res : a) -> Inf (MachineIO (state2Fn res)))
         -> MachineIO state1

  namespace MachineIO
    (>>=) : MachineCmd a state1 state2Fn
            -> ((res : a) -> Inf (MachineIO (state2Fn res)))
            -> MachineIO state1
    (>>=) = Do

  mutual
    vend : MachineIO (pounds, chocs)
    vend {pounds = S p} {chocs = S c} = do
      Vend
      Display "Enjoy!"
      machineLoop
    vend {pounds = Z} = do
      Display "Insert a coin"
      machineLoop
    vend {chocs = Z} = do
      Display "Out of stock"
      machineLoop

    refill : (num : Nat) -> MachineIO (pounds, chocs)
    refill {pounds = Z} num = do Refill num; machineLoop
    refill _ = do Display "Can't refill: Coins in machine"; machineLoop

    machineLoop : MachineIO (pounds, chocs)
    machineLoop = do
      Just x <- GetInput | Nothing => do Display "Invalid input"; machineLoop
      case x of
        COIN => do 
          coinRes <- InsertCoin
          case coinRes of
            OK => machineLoop
            Rejected => do Display "Invalid coin"; machineLoop
        VEND => vend
        CHANGE => do GetCoins; Display "Change returned"; machineLoop
        REFILL num => refill num
