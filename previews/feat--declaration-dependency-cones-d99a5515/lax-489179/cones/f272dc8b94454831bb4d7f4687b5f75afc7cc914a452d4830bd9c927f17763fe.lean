-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.SetTheory.Cardinal.Finite

-- Lax489179.Algorithms
section
namespace Lax489179
end Lax489179

namespace Lax489179.Algorithms
end Lax489179.Algorithms

namespace Lax489179.Algorithms.Mode
end Lax489179.Algorithms.Mode

namespace Lax489179.Algorithms.Mode.deterministic
end Lax489179.Algorithms.Mode.deterministic

namespace Lax489179.Algorithms.Mode.randomized
end Lax489179.Algorithms.Mode.randomized
end

-- Lax489179.TuringMachine
section
namespace Lax489179.TuringMachine.init
end Lax489179.TuringMachine.init

namespace Lax489179.TuringMachine.run
end Lax489179.TuringMachine.run

namespace Lax489179.TuringMachine

inductive Move
  | left
  | stay
  | right

def Move.offset : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

inductive Instruction (tapes symbols states : ℕ)
  | halt (answer : Bool)
  | next (state : Fin states) (write : Fin tapes → Fin symbols)
      (move : Fin tapes → Move)

/-- The added constants ensure a nonempty control and tape set and
three distinct input/blank symbols. -/
structure Machine where
  tapes : ℕ
  symbols : ℕ
  states : ℕ
  transition : Fin (states + 1) → (Fin (tapes + 1) → Fin (symbols + 3)) →
    Bool → Instruction (tapes + 1) (symbols + 3) (states + 1)

structure Config (M : Machine) where
  state : Fin (M.states + 1)
  head : Fin (M.tapes + 1) → ℤ
  tape : Fin (M.tapes + 1) → ℤ → Fin (M.symbols + 3)
  answer : Option Bool

/-- A halted configuration is unchanged, allowing a run to be padded. -/
def step (M : Machine) (coin : Bool) (c : Config M) : Config M :=
  match c.answer with
  | some _ => c
  | none =>
    match M.transition c.state (fun j => c.tape j (c.head j)) coin with
    | .halt b => { c with answer := some b }
    | .next q write move =>
      { state := q
        head := fun j => c.head j + (move j).offset
        tape := fun j z => if z = c.head j then write j else c.tape j z
        answer := none }

end Lax489179.TuringMachine
end
