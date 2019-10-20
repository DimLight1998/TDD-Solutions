-- 1
namespace Door
  data DoorState = DoorClosed | DoorOpen

  data DoorCmd : Type -> DoorState -> DoorState -> Type where
    Open : DoorCmd () DoorClosed DoorOpen
    Close : DoorCmd () DoorOpen DoorClosed
    RingBell : DoorCmd () state state
    (>>=) : DoorCmd a s1 s2 -> (a -> DoorCmd b s2 s3) -> DoorCmd b s1 s3

-- 2
namespace Guess
  data GuessCmd : Type -> Nat -> Nat -> Type where
    Try : Integer -> GuessCmd Ordering (S k) k
    Pure : ty -> GuessCmd ty s s
    (>>=) : GuessCmd a s1 s2 -> (a -> GuessCmd b s2 s3) -> GuessCmd b s1 s3

-- 3
namespace Matter
  data Matter = Solid | Liquid | Gas
  data MatterCmd : Type -> Matter -> Matter -> Type where
    Melt : MatterCmd () Solid Liquid
    Boil : MatterCmd () Liquid Gas
    Condense : MatterCmd () Gas Liquid
    Freeze : MatterCmd () Liquid Solid
    (>>=) : MatterCmd a s1 s2 -> (a -> MatterCmd b s2 s3) -> MatterCmd b s1 s3
