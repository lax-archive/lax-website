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

end Lax429075.CNF
end

-- Lax429075.Encoding
section
namespace Lax429075.Encoding

open CNF Lax434930.PolynomialTime

def encodeList {α : Type} (encode : α → Word) : List α → Word
  | [] => [false]
  | a :: as => true :: (encode a ++ encodeList encode as)

def encodeNat (n : ℕ) : Word := List.replicate n true ++ [false]

def encodeLiteral (l : Literal) : Word := encodeNat l.index ++ [l.positive]

def encodeClause : Clause → Word := encodeList encodeLiteral

def encodeCNF : Formula → Word := encodeList encodeClause

def parseNat : Word → Option (ℕ × Word)
  | [] => none
  | false :: w => some (0, w)
  | true :: w => do
    let (n, rest) ← parseNat w
    pure (n + 1, rest)

def parseLiteral (w : Word) : Option (Literal × Word) := do
  let (n, rest) ← parseNat w
  match rest with
  | [] => none
  | sign :: tail => pure (⟨n, sign⟩, tail)

def parseList {α : Type} (parse : Word → Option (α × Word)) :
    ℕ → Word → Option (List α × Word)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: w => some ([], w)
  | fuel + 1, true :: w => do
    let (a, rest) ← parse w
    let (as, tail) ← parseList parse fuel rest
    pure (a :: as, tail)

def parseClause (w : Word) : Option (Clause × Word) := parseList parseLiteral w.length w

def decodeCNF (w : Word) : Option Formula := do
  let (F, rest) ← parseList parseClause w.length w
  if rest = [] then pure F else none

end Lax429075.Encoding
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

/-- The formula a word stands for: the decoded one, or one empty clause if the word encodes
no formula. -/
def parseF (w : Word) : Formula := (decodeCNF w).getD [[]]

/-- The reduction on words. -/
def reduce (w : Word) : Word := encodeCNF (transform (parseF w))

end Lax345332.Construction
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

end Formula

/-- A formula as a binary word: the number of variables, the numbers of clauses of two and of
three literals, then the variable and sign of each literal of each clause, the clauses of
two literals first. -/
def encodeFormula (φ : Formula) : Word :=
  encodeNat φ.vars ++ encodeNat φ.twoClauses ++ encodeNat φ.threeClauses ++
    ((List.finRange φ.twoClauses).flatMap fun c =>
      (List.finRange 2).flatMap fun α => encodeNat (φ.aLit c α).1 ++ [(φ.aLit c α).2]) ++
    (List.finRange φ.threeClauses).flatMap fun c =>
      (List.finRange 3).flatMap fun α => encodeNat (φ.bLit c α).1 ++ [(φ.bLit c α).2]

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

/-- The construction on words: decode a formula, apply `build`, and encode the result. -/
def toBounded (w : Word) : Word := encodeFormula (build (parseF w))

/-- The reduction from satisfiability: the first reduction, then the construction. -/
def reduceB : Word → Word := toBounded ∘ reduce

end Lax345332.Copies
end
