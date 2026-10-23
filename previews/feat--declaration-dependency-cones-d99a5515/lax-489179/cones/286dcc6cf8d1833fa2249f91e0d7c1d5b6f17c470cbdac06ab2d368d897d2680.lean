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
namespace Lax489179.TuringMachine.run
end Lax489179.TuringMachine.run

namespace Lax489179.TuringMachine.step
end Lax489179.TuringMachine.step

namespace Lax489179.TuringMachine.Move.offset
end Lax489179.TuringMachine.Move.offset

namespace Lax489179.TuringMachine

inductive Move
  | left
  | stay
  | right

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

def init (M : Machine) (input : List Bool) : Config M where
  state := 0
  head := fun _ => 0
  tape := fun j z =>
    if j = 0 ∧ 0 ≤ z then
      match input[z.toNat]? with
      | none => 0
      | some false => 1
      | some true => 2
    else 0
  answer := none

end Lax489179.TuringMachine
end
