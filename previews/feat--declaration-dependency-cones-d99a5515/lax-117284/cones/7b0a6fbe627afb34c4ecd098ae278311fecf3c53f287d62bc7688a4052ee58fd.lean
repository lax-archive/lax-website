-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Order.Interval.Set.Basic

-- Lax117284.Scheduling
section
namespace Lax117284
end Lax117284

namespace Lax117284.Scheduling
end Lax117284.Scheduling

namespace Lax117284.Scheduling.Instance
end Lax117284.Scheduling.Instance
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

-- Lax429075.Reductions
section
namespace Lax429075.Reductions

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

def ManyOne (A B : Language) : Prop :=
  ∃ f : Word → Word, Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ x, x ∈ A ↔ f x ∈ B

end Lax429075.Reductions
end

-- Lax117284.Problems
section
namespace Lax117284.Problems

open Lax117284.Scheduling Lax434930.PolynomialTime

open Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- A language is **NP-hard** if every language in NP reduces to it in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ A : Language, A ∈ NP → ManyOne A L

end Lax117284.Problems
end

-- Lax117284.BoundedSat
section
namespace Lax117284.BoundedSat

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A **[2,3]-bounded 3-SAT formula** over `vars` variables: `twoClauses` clauses of two
literals and `threeClauses` clauses of three literals, in which every literal — a variable
together with a sign — occupies at most two of the positions of the formula. -/
structure Formula where
  /-- The number of variables. -/
  vars : ℕ
  /-- The number of clauses of two literals. -/
  twoClauses : ℕ
  /-- The number of clauses of three literals. -/
  threeClauses : ℕ
  /-- The literals of the clauses of two literals. -/
  aLit : Fin twoClauses → Fin 2 → Fin vars × Bool
  /-- The literals of the clauses of three literals. -/
  bLit : Fin threeClauses → Fin 3 → Fin vars × Bool
  /-- Every literal occurs at most twice in the formula. -/
  occ_le_two : ∀ l : Fin vars × Bool,
    (Finset.univ.filter fun o : (Fin twoClauses × Fin 2) ⊕ (Fin threeClauses × Fin 3) =>
      Sum.elim (fun q => aLit q.1 q.2) (fun q => bLit q.1 q.2) o = l).card ≤ 2

namespace Formula

variable (φ : Formula)

/-- An assignment of a truth value to every variable. -/
abbrev Assignment := Fin φ.vars → Bool

/-- The assignment `a` satisfies `φ`: every clause, of either width, has a literal that
holds. -/
def Satisfies (a : φ.Assignment) : Prop :=
  (∀ c, ∃ α, a (φ.aLit c α).1 = (φ.aLit c α).2) ∧
  (∀ c, ∃ α, a (φ.bLit c α).1 = (φ.bLit c α).2)

/-- **The question of [2,3]-bounded 3-SAT**: is there a satisfying assignment? -/
def Satisfiable : Prop := ∃ a : φ.Assignment, φ.Satisfies a

end Formula

/-- The number of occurrence slots of the formula. -/
def slots (φ : Formula) : ℕ := 2 * φ.twoClauses + 3 * φ.threeClauses

/-- A [2,3]-bounded 3-SAT formula as a binary word: the number of variables, the two
numbers of clauses, and then the variable and the sign of every literal of every clause,
the clauses of two literals first. -/
def encodeFormula (φ : Formula) : Word :=
  Problems.encodeNat φ.vars ++ Problems.encodeNat φ.twoClauses ++
    Problems.encodeNat φ.threeClauses ++
    ((List.finRange φ.twoClauses).flatMap fun c =>
      (List.finRange 2).flatMap fun α =>
        Problems.encodeNat (φ.aLit c α).1 ++ [(φ.aLit c α).2]) ++
    (List.finRange φ.threeClauses).flatMap fun c =>
      (List.finRange 3).flatMap fun α =>
        Problems.encodeNat (φ.bLit c α).1 ++ [(φ.bLit c α).2]

/-- **[2,3]-bounded 3-SAT**, as a language: the satisfiable formulas that have no more
variables than positions, which every formula in which each variable occurs does. -/
def BoundedSat : Language :=
  {w | ∃ φ : Formula, encodeFormula φ = w ∧ φ.vars ≤ slots φ ∧ φ.Satisfiable}

/-- **[2,3]-bounded 3-SAT is NP-hard.** -/
axiom boundedSat_npHard : Problems.NPHard BoundedSat

end Lax117284.BoundedSat
end
