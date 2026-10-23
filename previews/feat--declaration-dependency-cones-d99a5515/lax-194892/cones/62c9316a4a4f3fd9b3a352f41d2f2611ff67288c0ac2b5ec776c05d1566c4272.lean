-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

-- Lax194892.ForTransducers
section
namespace Lax194892.ForTransducers.forLoopRun
end Lax194892.ForTransducers.forLoopRun

namespace Lax194892.ForTransducers.ForProg.exec
end Lax194892.ForTransducers.ForProg.exec

namespace Lax194892.ForTransducers.ForProg.nestLoops
end Lax194892.ForTransducers.ForProg.nestLoops

namespace Lax194892.ForTransducers.ForTest.Holds
end Lax194892.ForTransducers.ForTest.Holds

namespace Lax194892.ForTransducers

/-- Tests of a for-transducer. -/
inductive ForTest (A : Type) : Type
  /-- The value of a Boolean variable. -/
  | boolVar : ℕ → ForTest A
  /-- The equality test `x == y` on position variables. -/
  | eqPos : ℕ → ℕ → ForTest A
  /-- The order test `x <= y` on position variables. -/
  | lePos : ℕ → ℕ → ForTest A
  /-- The label test `w[x] == a`. -/
  | label : ℕ → A → ForTest A
  /-- Negation. -/
  | not : ForTest A → ForTest A
  /-- Conjunction. -/
  | and : ForTest A → ForTest A → ForTest A
  /-- Disjunction. -/
  | or : ForTest A → ForTest A → ForTest A

/-- Programs of a for-transducer. -/
inductive ForProg (A B : Type) : Type
  /-- The empty program. -/
  | skip : ForProg A B
  /-- `output(b)`. -/
  | output : B → ForProg A B
  /-- `X = true` / `X = false`. -/
  | assign : ℕ → Bool → ForProg A B
  /-- Sequential composition `I ; J`. -/
  | seq : ForProg A B → ForProg A B → ForProg A B
  /-- A conditional. -/
  | ite : ForTest A → ForProg A B → ForProg A B → ForProg A B
  /-- `for x in positions(w)` (`true`) or `for x in positions_reverse(w)` (`false`). -/
  | loop : Bool → ℕ → ForProg A B → ForProg A B

namespace ForTest

variable {A : Type}

end ForTest

namespace ForProg

variable {A B : Type}

/-- A program without loops. -/
def LoopFree : ForProg A B → Prop
  | skip => True
  | output _ => True
  | assign _ _ => True
  | seq P Q => LoopFree P ∧ LoopFree Q
  | ite _ P Q => LoopFree P ∧ LoopFree Q
  | loop _ _ _ => False

end ForProg

end Lax194892.ForTransducers
end
