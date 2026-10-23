-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype

-- Lax434930.PolynomialTime
section
namespace Lax434930.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair

namespace Lax434930.Certificates

open PolynomialTime

/-- A self-delimiting encoding of the first string, followed by the second. -/
def pair : Word → Word → Word
  | [], y => true :: y
  | b :: x, y => false :: b :: pair x y

end Lax434930.Certificates
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Lax434930.NondeterministicPolynomialTime
end

-- Lax759944.BinaryWordEncoding
section
set_option backward.isDefEq.respectTransparency false

namespace Lax759944.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

/-- Encode one natural number, including the separator which begins it. -/
def encodeNat (n : ℕ) : List Symbol :=
  .separator :: n.bits.map (fun b => if b then .one else .zero)

/-- The canonical binary encoding of a finite list of natural numbers. -/
def encode (x : List ℕ) : List Symbol :=
  x.flatMap encodeNat

end Lax759944.BinaryWordEncoding
end

-- Lax759944.TuringPolytime
section
namespace Lax759944.TuringPolytime

open Lax759944.BinaryWordEncoding

/-- Polynomial-time computation, on the canonical binary word encoding, by
a finite multi-tape Turing machine. -/
def TuringPolytime (f : List ℕ → List ℕ) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encode encode f)

end Lax759944.TuringPolytime
end

-- Lax47.Machine
section
set_option autoImplicit false

namespace Lax47.Machine

open Lax759944.BinaryWordEncoding Lax759944.TuringPolytime

/-- A finite machine word.  Boolean data use the entries $0$ and $1$. -/
abbrev BitString := List ℕ

/-- The convenient monomial bound $c(n+1)^k$. -/
def polynomialBound (c k n : ℕ) : ℕ :=
  c * (n + 1) ^ k

/-- A total word function computed in polynomial time by a finite Turing machine. -/
structure PolytimeProgram where
  function : BitString → BitString
  polytime : TuringPolytime function

/-- The semantic output certified by the program's finite Turing machine. -/
def PolytimeProgram.output (program : PolytimeProgram)
    (input : BitString) : BitString :=
  program.function input

/-- A length-prefixed pairing of two finite words. -/
def pairBits (left right : BitString) : BitString :=
  left.length :: left ++ right

/-- A uniformly random string of exactly $r$ bits. -/
abbrev RandomSeed (r : ℕ) := Fin r → Bool

/-- Encode one Boolean as a natural-number word. -/
def bitWord (bit : Bool) : ℕ :=
  if bit then 1 else 0

/-- The word representation of a fixed-length random seed. -/
def RandomSeed.bits {r : ℕ} (seed : RandomSeed r) : BitString :=
  (List.ofFn seed).map bitWord

end Lax47.Machine
end

-- Lax47.Complexity
section
namespace Lax47.Complexity.TriangleFreeMISApproximation
end Lax47.Complexity.TriangleFreeMISApproximation

set_option autoImplicit false

namespace Lax47.Complexity

open Lax47.Machine

export Lax47.Machine
  (BitString RandomSeed PolytimeProgram polynomialBound pairBits)

/-- An executable simple graph on the labeled vertex set $\operatorname{Fin}(n)$. -/
structure GraphCode (n : ℕ) where
  adjacent : Fin n → Fin n → Bool
  loopless : ∀ vertex, adjacent vertex vertex = false
  symmetric : ∀ left right, adjacent left right = adjacent right left

/-- The mathematical simple graph represented by a Boolean adjacency matrix. -/
def GraphCode.graph {n : ℕ} (code : GraphCode n) : SimpleGraph (Fin n) where
  Adj left right := code.adjacent left right = true
  symm := ⟨fun left right h ↦ by
    rw [← code.symmetric]
    exact h⟩
  loopless := ⟨fun vertex ↦ by
    simp [code.loopless]⟩

/-- Vertex count followed by the row-major adjacency matrix. -/
def GraphCode.bits {n : ℕ} (code : GraphCode n) : BitString :=
  n :: List.ofFn fun rank : Fin (n * n) ↦
    let vertex := finProdFinEquiv.symm rank
    bitWord (code.adjacent vertex.1 vertex.2)

end Lax47.Complexity
end

-- Lax47.Gap
section
set_option autoImplicit false

namespace Lax47.Gap

open Lax47.Machine Lax47.Complexity

/-- A polynomial-time finite-Turing program with one fixed monomial tape bound. -/
structure GapProgram (q : ℕ) where
  program : PolytimeProgram
  randomnessConstant : ℕ
  randomnessExponent : ℕ
  randomnessConstant_pos : 0 < randomnessConstant

/-- The exact, uniformly specified random-tape length on order $n$. -/
def GapProgram.randomBitCount {q : ℕ} (program : GapProgram q) (n : ℕ) : ℕ :=
  polynomialBound program.randomnessConstant program.randomnessExponent n

/-- Finite uniform seed type read by a gap program on an $n$-vertex graph. -/
abbrev GapProgram.Seed {q : ℕ} (program : GapProgram q) (n : ℕ) :=
  RandomSeed (program.randomBitCount n)

/-- Boolean answer returned by the program's certified Turing computation. -/
def GapProgram.accepts {q : ℕ} (program : GapProgram q) (n : ℕ)
    (input : GraphCode n) (seed : program.Seed n) : Bool :=
  decide (program.program.output (pairBits input.bits seed.bits) = [1])

/-- Uniform seed enumeration for a finite-Turing program. -/
def GapProgram.seeds {q : ℕ} (program : GapProgram q) (n : ℕ) :
    Finset (program.Seed n) :=
  Finset.univ

/-- Seeds on which the finite-Turing program returns true. -/
def GapProgram.acceptingSeeds {q : ℕ} (program : GapProgram q)
    (n : ℕ) (input : GraphCode n) : Finset (program.Seed n) :=
  (program.seeds n).filter fun seed ↦ program.accepts n input seed

/--
A bounded-error finite-Turing polynomial-time solver for Håstad's rational
promise gap. The uniform random-tape length is the fixed monomial stored in
the gap program.
-/
structure MISGapSolver (q : ℕ) where
  program : GapProgram q
  cutoff : ℕ
  completeness : ∀ (n : ℕ), cutoff ≤ n → ∀ input : GraphCode n,
    Real.rpow n (1 - (q : ℝ)⁻¹) ≤ (input.graph.indepNum : ℝ) →
      2 * (program.seeds n).card ≤
        3 * (program.acceptingSeeds n input).card
  soundness : ∀ (n : ℕ), cutoff ≤ n → ∀ input : GraphCode n,
    (input.graph.indepNum : ℝ) ≤ Real.rpow n ((q : ℝ)⁻¹) →
      3 * (program.acceptingSeeds n input).card ≤
        (program.seeds n).card

end Lax47.Gap
end

-- Lax666725.ProbabilisticMachines
section
namespace Lax666725.ProbabilisticMachines

open Lax434930.PolynomialTime Turing

/-- Two finite local transition tables, with common halting configurations. -/
structure Machine where
  Γ : Type
  Q : Type
  [alphabet : Fintype Γ]
  [control : Fintype Q]
  [blank : Inhabited Γ]
  [initial : Inhabited Q]
  input : Bool ↪ Γ
  input_ne_blank : ∀ b, input b ≠ default
  transition : Bool → TM0.Machine Γ Q
  same_halts : ∀ q a, transition false q a = none ↔ transition true q a = none

attribute [instance] Machine.alphabet Machine.control Machine.blank Machine.initial

/-- Perform one coin-selected transition, keeping terminal configurations fixed. -/
def Machine.advance (M : Machine) (c : TM0.Cfg M.Γ M.Q) (b : Bool) :
    TM0.Cfg M.Γ M.Q :=
  (TM0.step (M.transition b) c).getD c

/-- Execute a finite sequence of fair coin choices. -/
def Machine.run (M : Machine) (x coins : Word) : TM0.Cfg M.Γ M.Q :=
  coins.foldl M.advance (TM0.init (x.map M.input))

/-- A uniform procedure with a worst-case polynomial bound on every branch. -/
structure Procedure (α : Type) where
  machine : Machine
  time : Polynomial ℕ
  output : machine.Q → α
  halts : ∀ (x : Word) (r : Fin (time.eval x.length) → Bool),
    TM0.step (machine.transition false) (machine.run x (List.ofFn r)) = none

/-- The finite sample space of coin sequences on a particular input. -/
abbrev Procedure.Coins {α : Type} (A : Procedure α) (x : Word) :=
  Fin (A.time.eval x.length) → Bool

/-- Read the output from the terminal control state. -/
def Procedure.eval {α : Type} (A : Procedure α) (x : Word) (r : A.Coins x) : α :=
  A.output (A.machine.run x (List.ofFn r)).q

/-- Exact probability under independent uniform bits. -/
noncomputable def Procedure.probability {α : Type} (A : Procedure α)
    (x : Word) (E : α → Prop) : ℚ := by
  classical
  exact ((Finset.univ.filter (fun r : A.Coins x => E (A.eval x r))).card : ℚ) /
    Fintype.card (A.Coins x)

/-- A Boolean answer correctly decides membership of the given input. -/
def Correct (L : Language) (x : Word) (b : Bool) : Prop :=
  (b = true ↔ x ∈ L)

end Lax666725.ProbabilisticMachines
end

-- Lax666725.RandomizedPolynomialTime
section
namespace Lax666725.RandomizedPolynomialTime

open Lax434930.PolynomialTime ProbabilisticMachines

def BPP : Set Language :=
  {L | ∃ A : Procedure Bool, ∀ x, (2 / 3 : ℚ) ≤ A.probability x (Correct L x)}

end Lax666725.RandomizedPolynomialTime
end

-- Lax47.IndependentSetGapHardness
section
set_option autoImplicit false

namespace Lax47.IndependentSetGapHardness

open Lax47.Gap

open Lax434930.NondeterministicPolynomialTime

open Lax666725.RandomizedPolynomialTime

/-- Håstad's general-graph promise-gap inapproximability theorem. -/
axiom gapSolver_implies_np_subset_bpp :
  ∀ q : ℕ, 3 ≤ q → MISGapSolver q → NP ⊆ BPP

end Lax47.IndependentSetGapHardness
end
