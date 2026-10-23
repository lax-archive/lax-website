-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

-- Lax194892.ForTransducers
section
namespace Lax194892.ForTransducers.forLoopRun
end Lax194892.ForTransducers.forLoopRun

namespace Lax194892.ForTransducers.ForProg.LoopFree
end Lax194892.ForTransducers.ForProg.LoopFree

namespace Lax194892.ForTransducers.ForProg.assign
end Lax194892.ForTransducers.ForProg.assign

namespace Lax194892.ForTransducers.ForProg.exec
end Lax194892.ForTransducers.ForProg.exec

namespace Lax194892.ForTransducers.ForProg.ite
end Lax194892.ForTransducers.ForProg.ite

namespace Lax194892.ForTransducers.ForProg.loop
end Lax194892.ForTransducers.ForProg.loop

namespace Lax194892.ForTransducers.ForProg.nestLoops
end Lax194892.ForTransducers.ForProg.nestLoops

namespace Lax194892.ForTransducers.ForProg.output
end Lax194892.ForTransducers.ForProg.output

namespace Lax194892.ForTransducers.ForProg.seq
end Lax194892.ForTransducers.ForProg.seq

namespace Lax194892.ForTransducers.ForProg.skip
end Lax194892.ForTransducers.ForProg.skip

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

namespace ForTest

variable {A : Type}

/-- The truth value of a test under valuations of the position and Boolean
variables. -/
def Holds (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) : ForTest A → Prop
  | boolVar i => bv i = true
  | eqPos i j => pos i = pos j
  | lePos i j => pos i ≤ pos j
  | label i a => w[pos i]? = some a
  | not t => ¬ Holds w pos bv t
  | and t s => Holds w pos bv t ∧ Holds w pos bv s
  | or t s => Holds w pos bv t ∨ Holds w pos bv s

end ForTest

namespace ForProg

variable {A B : Type}

end ForProg

end Lax194892.ForTransducers
end
