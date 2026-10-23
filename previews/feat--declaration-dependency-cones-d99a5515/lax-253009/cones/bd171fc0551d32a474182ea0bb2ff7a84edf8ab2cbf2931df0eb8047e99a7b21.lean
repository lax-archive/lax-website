-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.FinRange
import Mathlib.Data.Rat.Defs

-- Lax253009.Graphs
section
namespace Lax253009.Graphs

structure Graph (n : ℕ) where
  adjacent : Fin n → Fin n → Bool
  loopless : ∀ v, adjacent v v = false
  symmetric : ∀ u v, adjacent u v = adjacent v u

def Graph.simpleGraph {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj u v := G.adjacent u v = true
  symm := ⟨fun u v h ↦ by rw [← G.symmetric]; exact h⟩
  loopless := ⟨fun v ↦ by simp [G.loopless]⟩

def Graph.encode {n : ℕ} (G : Graph n) : List Bool :=
  List.replicate n true ++ [false] ++
    (List.finRange n).flatMap (fun u ↦ (List.finRange n).map (G.adjacent u))

noncomputable def Graph.cliqueNumber {n : ℕ} (G : Graph n) : ℕ :=
  G.simpleGraph.cliqueNum

end Lax253009.Graphs
end

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

-- Lax253009.Approximation
section
namespace Lax253009.Approximation

open Graphs

open Lax434930.PolynomialTime

def Approximable (ε : ℝ) : Prop :=
  ∃ estimate : Word → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeNat estimate) ∧
    ∀ (n : ℕ), 0 < n → ∀ G : Graph n,
      estimate G.encode ≤ G.cliqueNumber ∧
      (G.cliqueNumber : ℝ) ≤ Real.rpow (n : ℝ) (1 - ε) * (estimate G.encode : ℝ)

end Lax253009.Approximation
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

-- Lax666725.ZeroError
section
namespace Lax666725.ZeroError

open Lax434930.PolynomialTime ProbabilisticMachines

def ZPP : Set Language :=
  {L | ∃ A : Procedure (Option Bool), ∀ x,
    (∀ r b, A.eval x r = some b → Correct L x b) ∧
    (2 / 3 : ℚ) ≤ A.probability x (fun a => a.isSome = true)}

end Lax666725.ZeroError
end

-- Lax253009.CliqueHardness
section
namespace Lax253009.CliqueHardness

open Approximation

open Lax434930.NondeterministicPolynomialTime Lax666725.ZeroError

axiom not_approximable (ε : ℝ) (hε : 0 < ε) (hne : NP ≠ ZPP) :
  ¬ Approximable ε

end Lax253009.CliqueHardness
end
