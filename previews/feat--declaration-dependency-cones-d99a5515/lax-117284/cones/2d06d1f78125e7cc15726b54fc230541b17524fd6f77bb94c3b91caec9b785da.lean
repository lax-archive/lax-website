-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Finite
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

-- Lax117284.MulticolouredIndepSet
section
namespace Lax117284.MulticolouredIndepSet

open Lax434930.PolynomialTime

/-- An instance of Multicoloured Independent Set: a graph on `colours` classes of `size`
vertices whose edges join vertices of different classes. -/
structure Instance where
  /-- The number `ℓ` of colour classes. -/
  colours : ℕ
  /-- The number `n` of vertices in each class. -/
  size : ℕ
  /-- The graph, on the vertices `(class, index)`. -/
  graph : SimpleGraph (Fin colours × Fin size)
  /-- Adjacent vertices lie in different classes. -/
  adj_colour_ne : ∀ u v, graph.Adj u v → u.1 ≠ v.1

namespace Instance

variable (G : Instance)

/-- **The question of Multicoloured Independent Set**: is there one vertex of every class
such that no two of them are adjacent? -/
def HasIndepSet : Prop :=
  ∃ f : Fin G.colours → Fin G.size, ∀ i i', ¬ G.graph.Adj (i, f i) (i', f i')

/-- The number `ℓn` of vertices. -/
def vertices : ℕ := G.colours * G.size

open Classical in
/-- Whether the vertices numbered `w` and `w'` are adjacent, and `false` for numbers that
name no vertex. -/
noncomputable def adjAt (w w' : ℕ) : Bool :=
  if h : w < G.vertices ∧ w' < G.vertices then
    have hs : 0 < G.size := by
      by_contra h0
      have hz : G.size = 0 := by omega
      rw [vertices, hz, Nat.mul_zero] at h
      omega
    decide (G.graph.Adj
      (⟨w / G.size, (Nat.div_lt_iff_lt_mul hs).2 h.1⟩, ⟨w % G.size, Nat.mod_lt _ hs⟩)
      (⟨w' / G.size, (Nat.div_lt_iff_lt_mul hs).2 h.2⟩, ⟨w' % G.size, Nat.mod_lt _ hs⟩))
  else false

/-- The neighbours of the vertex numbered `w`, in increasing order. -/
noncomputable def nbrs (w : ℕ) : List ℕ :=
  (List.range G.vertices).filter fun w' => G.adjAt w w'

/-- The edges, each listed as the pair of its endpoints from the smaller number to the
larger — which, since adjacent vertices lie in different classes, is from the smaller class
to the larger. -/
noncomputable def edgeList : List (ℕ × ℕ) :=
  (List.range G.vertices).flatMap fun w => ((G.nbrs w).filter fun w' => w < w').map (w, ·)

/-- The number `|E|` of edges. -/
noncomputable def edgeCount : ℕ := G.edgeList.length

/-- Every vertex of `G` has exactly `r` neighbours. -/
def Regular (r : ℕ) : Prop := ∀ w < G.vertices, (G.nbrs w).length = r

/-- The normal form the reduction into fair repetitive interval scheduling consumes: the
graph is regular of some positive degree, every class holds at least four vertices, and the
number of edges is even. -/
def Normal : Prop := (∃ r, 0 < r ∧ G.Regular r) ∧ 4 ≤ G.size ∧ 2 ∣ G.edgeCount

end Instance

/-- An instance as a binary word: the number of classes, the number of vertices per class,
and then the adjacency matrix, one bit per ordered pair of vertices. -/
noncomputable def encodeInstance (G : Instance) : Word :=
  Problems.encodeNat G.colours ++ Problems.encodeNat G.size ++
    (List.range G.vertices).flatMap fun w =>
      (List.range G.vertices).map fun w' => G.adjAt w w'

/-- **Multicoloured Independent Set on the instances in normal form**, as a language. -/
def NormalMulticolouredIndepSet : Language :=
  {w | ∃ G : Instance, encodeInstance G = w ∧ G.Normal ∧ G.HasIndepSet}

/-- **Multicoloured Independent Set is NP-hard on the instances in normal form.** -/
axiom normalMulticolouredIndepSet_npHard :
    Problems.NPHard NormalMulticolouredIndepSet

end Lax117284.MulticolouredIndepSet
end
