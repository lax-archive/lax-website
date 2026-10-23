-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

-- Lax194892.ForTransducers
section
namespace Lax194892.ForTransducers.ForProg.LoopFree
end Lax194892.ForTransducers.ForProg.LoopFree

namespace Lax194892.ForTransducers.ForProg.nestLoops
end Lax194892.ForTransducers.ForProg.nestLoops

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

/-- Running the body of a loop over a list of positions, threading the Boolean
valuation and concatenating the outputs. -/
def forLoopRun {B : Type} (body : (ℕ → Bool) → ℕ → (ℕ → Bool) × List B) :
    List ℕ → (ℕ → Bool) → (ℕ → Bool) × List B
  | [], bv => (bv, [])
  | p :: ps, bv =>
      let r := body bv p
      let r' := forLoopRun body ps r.1
      (r'.1, r.2 ++ r'.2)

namespace ForProg

variable {A B : Type}

open scoped Classical in
/-- The semantics of a program: the final Boolean valuation and the output. -/
noncomputable def exec (w : List A) :
    ForProg A B → (ℕ → ℕ) → (ℕ → Bool) → (ℕ → Bool) × List B
  | skip, _, bv => (bv, [])
  | output b, _, bv => (bv, [b])
  | assign i v, _, bv => (Function.update bv i v, [])
  | seq P Q, pos, bv =>
      let r := exec w P pos bv
      let r' := exec w Q pos r.1
      (r'.1, r.2 ++ r'.2)
  | ite t P Q, pos, bv =>
      if ForTest.Holds w pos bv t then exec w P pos bv else exec w Q pos bv
  | loop dir x P, pos, bv =>
      forLoopRun (fun bv' p => exec w P (Function.update pos x p) bv')
        (if dir then List.range w.length else (List.range w.length).reverse) bv

/-- The function computed by a for-transducer. -/
noncomputable def eval (P : ForProg A B) (w : List A) : List B :=
  (exec w P (fun _ => 0) (fun _ => false)).2

end ForProg

/-- A function computed by a for-transducer. -/
def IsForTransducer {A B : Type} (f : List A → List B) : Prop :=
  ∃ P : ForProg A B, ∀ w, P.eval w = f w

end Lax194892.ForTransducers
end
