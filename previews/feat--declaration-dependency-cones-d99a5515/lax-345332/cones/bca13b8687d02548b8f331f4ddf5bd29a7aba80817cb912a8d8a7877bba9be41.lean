-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

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

-- Lax429075.CNF
section
namespace Lax429075
end Lax429075

namespace Lax429075.CNF
end Lax429075.CNF

namespace Lax429075.CNF.Literal
end Lax429075.CNF.Literal
end

-- Lax429075.Encoding
section
namespace Lax429075.Encoding
end Lax429075.Encoding

namespace Lax429075.Encoding.decodeCNF
end Lax429075.Encoding.decodeCNF

namespace Lax429075.Encoding.encodeList
end Lax429075.Encoding.encodeList

namespace Lax429075.Encoding.parseList
end Lax429075.Encoding.parseList

namespace Lax429075.Encoding.parseLiteral
end Lax429075.Encoding.parseLiteral

namespace Lax429075.Encoding.parseNat
end Lax429075.Encoding.parseNat
end

-- Lax429075.Satisfiability
section
namespace Lax429075.Satisfiability
end Lax429075.Satisfiability
end

-- Lax345332.ThreeFourSat
section
namespace Lax345332
end Lax345332

namespace Lax345332.ThreeFourSat
end Lax345332.ThreeFourSat
end

-- Lax345332.TwoThreeSat
section
namespace Lax345332.TwoThreeSat

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

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

/-- The assignment `a` satisfies `φ`: every clause, of two or of three literals, contains a
literal that `a` makes true. -/
def Satisfies (a : φ.Assignment) : Prop :=
  (∀ c, ∃ α, a (φ.aLit c α).1 = (φ.aLit c α).2) ∧
  (∀ c, ∃ α, a (φ.bLit c α).1 = (φ.bLit c α).2)

/-- The formula has a satisfying assignment. -/
def Satisfiable : Prop := ∃ a : φ.Assignment, φ.Satisfies a

end Formula

/-- The number of literal positions: two per clause of two literals, three per clause of
three. -/
def slots (φ : Formula) : ℕ := 2 * φ.twoClauses + 3 * φ.threeClauses

/-- A formula as a binary word: the number of variables, the numbers of clauses of two and of
three literals, then the variable and sign of each literal of each clause, the clauses of
two literals first. -/
def encodeFormula (φ : Formula) : Word :=
  encodeNat φ.vars ++ encodeNat φ.twoClauses ++ encodeNat φ.threeClauses ++
    ((List.finRange φ.twoClauses).flatMap fun c =>
      (List.finRange 2).flatMap fun α => encodeNat (φ.aLit c α).1 ++ [(φ.aLit c α).2]) ++
    (List.finRange φ.threeClauses).flatMap fun c =>
      (List.finRange 3).flatMap fun α => encodeNat (φ.bLit c α).1 ++ [(φ.bLit c α).2]

/-- **[2,3]-bounded 3-SAT** as a language: the encodings of satisfiable formulas with at
most as many variables as literal positions. -/
def SAT23 : Language :=
  {w | ∃ φ : Formula, encodeFormula φ = w ∧ φ.vars ≤ slots φ ∧ φ.Satisfiable}

/-- **[2,3]-bounded 3-SAT is NP-hard.** Every language in NP has a polynomial-time
many-one reduction to it. -/
axiom npHard :
    ∀ A : Language, A ∈ NP → Lax429075.Reductions.ManyOne A SAT23

end Lax345332.TwoThreeSat
end
