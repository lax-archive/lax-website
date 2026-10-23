-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Computability.TuringMachine.Computable

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
namespace Lax345332.Construction

open Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime Lax345332.ThreeFourSat

/-- Tovey's thirteen clauses on the variables `g, g+1, …, g+9`; they force `g` to be true. -/
def gadget (g : ℕ) : Formula :=
  let y := g
  let a (j : ℕ) := g + 1 + 3 * j
  let b (j : ℕ) := g + 2 + 3 * j
  let d (j : ℕ) := g + 3 + 3 * j
  ((List.range 3).map fun j => [⟨y, true⟩, ⟨a j, true⟩, ⟨b j, true⟩]) ++
  ((List.range 3).flatMap fun j =>
    [[⟨d j, true⟩, ⟨a j, true⟩, ⟨b j, false⟩], [⟨d j, true⟩, ⟨a j, false⟩, ⟨b j, true⟩],
     [⟨d j, true⟩, ⟨a j, false⟩, ⟨b j, false⟩]]) ++
  [[⟨d 0, false⟩, ⟨d 1, false⟩, ⟨d 2, false⟩]]

/-- The base of the `t`-th gadget of the `k`-th clause, above the variables below `B`. -/
def ybase (B k t : ℕ) : ℕ := B + 30 * k + 10 * t

/-- The padding literals of a clause of length `n`. -/
def pads (B k n : ℕ) : Clause := (List.range (3 - n)).map fun t => ⟨ybase B k t, false⟩

/-- The `k`-th clause, padded, with its three gadgets. -/
def unit (B k : ℕ) (C : Clause) : Formula :=
  (C ++ pads B k C.length) ::
    (gadget (ybase B k 0) ++ gadget (ybase B k 1) ++ gadget (ybase B k 2))

/-- Every clause of `G`, padded to three literals and followed by its gadgets. `B` bounds the
variables in use. -/
def pad (B : ℕ) (G : Formula) : Formula :=
  (List.range G.length).flatMap fun k => unit B k (G.getD k [])

/-- The copy of the variable `v` at position `p`. -/
def wv (V v p : ℕ) : ℕ := v + p * V

/-- The link variable after position `p`. -/
def zv (V N p : ℕ) : ℕ := V * N + p

/-- A placeholder literal, used when an index is past the end of a list. -/
def dflt : Literal := ⟨0, false⟩

/-- The `i`-th clause of the chain of `C`, whose first literal sits at position `o`: the
negated link before it (except for `i = 0`), the copy of the `i`-th literal, and the link
after it (except for the last). -/
def chainClause (V N o : ℕ) (C : Clause) (i : ℕ) : Clause :=
  (if i = 0 then [] else [⟨zv V N (o + i - 1), false⟩]) ++
    [⟨wv V (C.getD i dflt).index (o + i), (C.getD i dflt).positive⟩] ++
    (if i + 1 = C.length then [] else [⟨zv V N (o + i), true⟩])

/-- The chain of the clause `C`, whose first literal sits at position `o`; an empty clause
becomes one empty clause. -/
def chainClauses (V N o : ℕ) (C : Clause) : Formula :=
  if C.length = 0 then [[]] else (List.range C.length).map (chainClause V N o C)

/-- The chains of all clauses of a formula, the first literal of the formula being at
position `o`. -/
def chains (V N : ℕ) : ℕ → Formula → Formula
  | _, [] => []
  | o, C :: F => chainClauses V N o C ++ chains V N (o + C.length) F

/-- The cyclic successor on positions. -/
def next (N p : ℕ) : ℕ := if p + 1 < N then p + 1 else 0

/-- The cycle clauses `w v (next p) → w v p`, one for every variable `v < V` and position
`p < N`. Their variables are numbered `k = w v p`. -/
def cycles (V N : ℕ) : Formula :=
  (List.range (V * N)).map fun k => [⟨k, true⟩, ⟨wv V (k % V) (next N (k / V)), false⟩]

/-- The number of literal occurrences of a formula. -/
def size (F : Formula) : ℕ := (F.map List.length).sum

/-- A strict bound on the variable indices of a formula (at least 1). -/
def bound : Formula → ℕ
  | [] => 1
  | C :: F => max (C.foldr (fun l b => max (l.index + 1) b) 1) (bound F)

/-- The splitting step: the chains of all clauses, then the cycle clauses. -/
def split (F : Formula) : Formula :=
  chains (bound F) (size F) 0 F ++ cycles (bound F) (size F)

/-- The reduction on formulas: split, then pad above every variable in use. -/
def transform (F : Formula) : Formula := pad (bound F * size F + size F) (split F)

/-- The image is satisfiable exactly when the formula is. -/
axiom transform_sat (F : Formula) : Satisfiable F ↔ Satisfiable (transform F)

end Lax345332.Construction
end
