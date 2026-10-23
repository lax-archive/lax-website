-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic

-- Lax920634.EdgeExpansion
section
namespace Lax920634
end Lax920634

namespace Lax920634.EdgeExpansion
end Lax920634.EdgeExpansion
end

-- Lax920634.SeedSearch
section
namespace Lax920634.SeedSearch

open Function

/-- A table of thirty maps on a numbered finite vertex set. -/
abbrev Table (n : ℕ) := Fin 30 → Fin n → Fin n

/-- The number of vertices of `S` whose image lies outside `S`. -/
def escape {n : ℕ} (f : Fin n → Fin n) (S : Finset (Fin n)) : ℕ :=
  (S.filter fun v => f v ∉ S).card

/-- Each row is a permutation, and some row moves at least a tenth of each small set out. -/
abbrev GoodTable {n : ℕ} (T : Table n) : Prop :=
  (∀ i, Bijective (T i)) ∧
    ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      ∃ i : Fin 30, S.card ≤ 10 * escape (T i) S

/-- The candidate table represented by a base-`n` integer. -/
def decode (n : ℕ) (code : Fin (n ^ (30 * n))) : Table n :=
  fun i v => finFunctionFinEquiv.symm code (finProdFinEquiv (i, v))

/-- All candidate codes in increasing numerical order. -/
def candidates (n : ℕ) : List (Fin (n ^ (30 * n))) := List.finRange _

/-- The first expanding permutation table found by the finite deterministic scan. -/
def selectedTable (n : ℕ) : Table n :=
  (((candidates n).find? fun code => decide (GoodTable (decode n code))).map
    (decode n)).getD (fun _ v => v)

/-- Find the inverse image by scanning a numbered finite vertex set. -/
def inverse {n : ℕ} (f : Fin n → Fin n) (v : Fin n) : Fin n :=
  ((List.finRange n).find? fun u => decide (f u = v)).getD v

/-- A fixed powering exponent sufficient for the lazy permutation seed. -/
def poweringExponent : ℕ := 5760000

/-- The fixed degree of the powered seed. -/
def seedDegree : ℕ := 120 ^ poweringExponent

/-- The fixed number of seed vertices, the fourth power of its degree. -/
def seedOrder : ℕ := seedDegree ^ 4

end Lax920634.SeedSearch
end

-- Lax920634.SeedRotation
section
namespace Lax920634.SeedRotation

open SeedSearch

/-- Number forward and inverse permutation darts by integers below sixty. -/
def permutationLabels : (Fin 30 × Bool) ≃ Fin 60 :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

/-- Number the permutation darts and the sixty stationary darts together. -/
def lazyLabels : ((Fin 30 × Bool) ⊕ Fin 60) ≃ Fin 120 :=
  (Equiv.sumCongr permutationLabels (Equiv.refl _)).trans finSumFinEquiv

/-- The rotation of the selected lazy permutation graph, with numbered labels. -/
def lazyRotation (n : ℕ) (p : Fin n × Fin 120) : Fin n × Fin 120 :=
  match lazyLabels.symm p.2 with
  | Sum.inl (i, false) =>
    (selectedTable n i p.1, lazyLabels (Sum.inl (i, true)))
  | Sum.inl (i, true) =>
    (inverse (selectedTable n i) p.1,
      lazyLabels (Sum.inl (i, false)))
  | Sum.inr j => (p.1, lazyLabels (Sum.inr j))

/-- Follow a finite sequence of numbered darts to its endpoint. -/
def walkEnd {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d) :
    (t : ℕ) → Fin n → (Fin t → Fin d) → Fin n
  | 0, v, _ => v
  | t + 1, v, s => walkEnd R t (R (v, s 0)).1 (fun j => s j.succ)

/-- The vertex reached after a prescribed number of steps of a finite dart sequence. -/
def walkAt {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (t : ℕ) (v : Fin n) (s : Fin t → Fin d) : ℕ → Fin n
  | 0 => v
  | k + 1 => if h : k < t then
    (R (walkAt R t v s k, s ⟨k, h⟩)).1 else walkAt R t v s k

/-- The edge rotation of a graph power, with dart sequences numbered in base `d`. -/
def powerRotation {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (t : ℕ) (p : Fin n × Fin (d ^ t)) : Fin n × Fin (d ^ t) :=
  let s := finFunctionFinEquiv.symm p.2
  (walkEnd R t p.1 s, finFunctionFinEquiv (fun j =>
    (R (walkAt R t p.1 s (Fin.rev j).val, s (Fin.rev j))).2))

/-- The fixed seed's rotation map, after lazy powering. -/
def rotation : Fin seedOrder × Fin seedDegree →
    Fin seedOrder × Fin seedDegree :=
  powerRotation (lazyRotation seedOrder) poweringExponent

end Lax920634.SeedRotation
end

-- Lax920634.ZigZagConstruction
section
namespace Lax920634.ZigZagConstruction

open SeedSearch

/-- The fixed degree of each regular graph in the tower. -/
def degree : ℕ := seedDegree ^ 2

/-- A total numerical query to the fixed seed's edge rotation. -/
def seedValue (p : ℕ × ℕ) : ℕ × ℕ :=
  if h : p.1 < seedOrder ∧ p.2 < seedDegree then
    let r := SeedRotation.rotation (⟨p.1, h.1⟩, ⟨p.2, h.2⟩)
    (r.1.val, r.2.val)
  else (0, 0)

/-- The regular tower's rotation, computed by squaring and zig-zag steps. -/
def rotation : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, (v, i) =>
      let p₀ := seedValue (v, i / seedDegree)
      let p₁ := seedValue (p₀.1, i % seedDegree)
      (p₁.1, p₀.2 + seedDegree * p₁.2)
  | k + 1, (v, i) =>
      let p := seedValue (v % seedDegree ^ 4, i / seedDegree)
      let q₀ := rotation k (v / seedDegree ^ 4, p.1 / degree)
      let q₁ := rotation k (q₀.1, p.1 % degree)
      let r := seedValue (q₀.2 + degree * q₁.2, i % seedDegree)
      (r.1 + seedDegree ^ 4 * q₁.1, p.2 + seedDegree * r.2)

/-- The matching endpoint of a port, in the canonical vertex numbering. -/
def matchingNeighbor (k v : ℕ) : ℕ :=
  let r := rotation k (v / degree, v % degree)
  r.2 + degree * r.1

end Lax920634.ZigZagConstruction
end
