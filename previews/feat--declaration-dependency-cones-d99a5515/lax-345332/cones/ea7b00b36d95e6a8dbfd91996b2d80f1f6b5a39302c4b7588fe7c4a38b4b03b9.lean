-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

-- Lax434930.PolynomialTime
section
namespace Lax434930
end Lax434930

namespace Lax434930.PolynomialTime
end Lax434930.PolynomialTime
end

-- Lax434930.Certificates
section
namespace Lax434930.Certificates
end Lax434930.Certificates

namespace Lax434930.Certificates.pair
end Lax434930.Certificates.pair

namespace Lax434930.Certificates.unpair
end Lax434930.Certificates.unpair
end

-- Lax434930.NondeterministicPolynomialTime
section
namespace Lax434930.NondeterministicPolynomialTime
end Lax434930.NondeterministicPolynomialTime
end

-- Lax429075.Reductions
section
namespace Lax429075
end Lax429075

namespace Lax429075.Reductions
end Lax429075.Reductions
end

-- Lax429075.CNF
section
namespace Lax429075.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

abbrev Clause := List Literal

abbrev Formula := List Clause

abbrev Assignment := ℕ → Bool

def Literal.eval (l : Literal) (ρ : Assignment) : Bool :=
  if l.positive then ρ l.index else !(ρ l.index)

def eval (F : Formula) (ρ : Assignment) : Bool :=
  F.all fun C => C.any fun l => l.eval ρ

def Satisfiable (F : Formula) : Prop := ∃ ρ, eval F ρ = true

end Lax429075.CNF
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

-- Lax345332.Construction
section
namespace Lax345332.Construction.chains
end Lax345332.Construction.chains

namespace Lax345332.Construction

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax345332.ThreeFourSat

/-- The copy of the variable `v` at position `p`. -/
def wv (V v p : ℕ) : ℕ := v + p * V

/-- A placeholder literal, used when an index is past the end of a list. -/
def dflt : Literal := ⟨0, false⟩

/-- The cyclic successor on positions. -/
def next (N p : ℕ) : ℕ := if p + 1 < N then p + 1 else 0

/-- A strict bound on the variable indices of a formula (at least 1). -/
def bound : Formula → ℕ
  | [] => 1
  | C :: F => max (C.foldr (fun l b => max (l.index + 1) b) 1) (bound F)

end Lax345332.Construction
end

-- Lax345332.TwoThreeSat
section
namespace Lax345332.TwoThreeSat

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

/-- The assignment `a` satisfies `φ`: every clause, of two or of three literals, contains a
literal that `a` makes true. -/
def Satisfies (a : φ.Assignment) : Prop :=
  (∀ c, ∃ α, a (φ.aLit c α).1 = (φ.aLit c α).2) ∧
  (∀ c, ∃ α, a (φ.bLit c α).1 = (φ.bLit c α).2)

/-- The formula has a satisfying assignment. -/
def Satisfiable : Prop := ∃ a : φ.Assignment, φ.Satisfies a

end Formula

end Lax345332.TwoThreeSat
end

-- Lax345332.Copies
section
namespace Lax345332.Copies

open Lax429075.CNF Lax345332.Construction Lax345332.TwoThreeSat Lax434930.PolynomialTime

/-- The literal at position `p` of the flattened formula, and a default literal past its
end. -/
def litAt (F : Lax429075.CNF.Formula) (p : ℕ) : Literal := (F.flatMap id).getD p dflt

/-- The number of literal positions: three per clause. -/
def npos (F : Lax429075.CNF.Formula) : ℕ := 3 * F.length

/-- The number of variables of the result: one copy for every variable and position. -/
def nvars (F : Lax429075.CNF.Formula) : ℕ := bound F * npos F

/-- The copy of the variable at position `p`. -/
def copyVar (F : Lax429075.CNF.Formula) (p : ℕ) : ℕ := wv (bound F) (litAt F p).index p

/-- The copy that the cycle clause of `kk` mentions negatively: the same variable at the
next position. -/
def succVar (V N kk : ℕ) : ℕ := wv V (kk % V) (next N (kk / V))

/-- The bound on the variables is positive, which the `Fin` indices need. -/
theorem bound_pos (F : Lax429075.CNF.Formula) : 0 < bound F := by
  induction F with
  | nil => exact Nat.one_pos
  | cons C F ih => exact lt_of_lt_of_le ih (le_max_right _ _)

/-- The literals of the cycle clause `kk`: the copy `kk`, and the negation of its
successor. -/
def twoLit (F : Lax429075.CNF.Formula) (kk : Fin (nvars F)) (α : Fin 2) :
    Fin (nvars F) × Bool :=
  if α.val = 0 then (kk, true)
  else (⟨succVar (bound F) (npos F) kk.val % nvars F, Nat.mod_lt _ kk.pos⟩, false)

/-- The literals of clause `c`: for `t < 3`, the copy at position `3c + t`, with the sign of
the original literal. -/
def threeLit (F : Lax429075.CNF.Formula) (c : Fin F.length) (t : Fin 3) :
    Fin (nvars F) × Bool :=
  (⟨copyVar F (3 * c.val + t.val) % nvars F,
      Nat.mod_lt _ (Nat.mul_pos (bound_pos F) (Nat.mul_pos (by decide) c.pos))⟩,
    (litAt F (3 * c.val + t.val)).positive)

/-- The occurrence condition on the construction: every literal occupies at most two
positions. -/
def Occ (F : Lax429075.CNF.Formula) : Prop :=
  ∀ l : Fin (nvars F) × Bool,
    (Finset.univ.filter fun o : (Fin (nvars F) × Fin 2) ⊕ (Fin F.length × Fin 3) =>
      Sum.elim (fun q => twoLit F q.1 q.2) (fun q => threeLit F q.1 q.2) o = l).card ≤ 2

instance (F : Lax429075.CNF.Formula) : Decidable (Occ F) := by unfold Occ; infer_instance

/-- The formula with no variable and no clause. -/
def empty : Lax345332.TwoThreeSat.Formula :=
  ⟨0, 0, 0, fun c => c.elim0, fun c => c.elim0, fun l => l.1.elim0⟩

/-- **The construction.** It has `V·N` variables, where `V` bounds the variables of `F` and
`N = 3C` is its number of positions; the `V·N` cycle clauses; and the `C` clauses of three
literals on the copies. It is the empty formula if the occurrence condition fails. -/
def build (F : Lax429075.CNF.Formula) : Lax345332.TwoThreeSat.Formula :=
  if h : Occ F then ⟨nvars F, nvars F, F.length, twoLit F, threeLit F, h⟩ else empty

/-- Every clause of the formula has exactly three literals. -/
def Three (F : Lax429075.CNF.Formula) : Prop := ∀ C ∈ F, C.length = 3

/-- On a formula whose clauses all have three literals, the construction is satisfiable
exactly when the formula is. -/
axiom build_sat (F : Lax429075.CNF.Formula) (h : Three F) :
    Satisfiable F ↔ (build F).Satisfiable

end Lax345332.Copies
end
