-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

-- Lax350013.WordRAM
section
namespace Lax350013
end Lax350013

namespace Lax350013.WordRAM
end Lax350013.WordRAM

namespace Lax350013.WordRAM.Instr
end Lax350013.WordRAM.Instr

namespace Lax350013.WordRAM.exec
end Lax350013.WordRAM.exec

namespace Lax350013.WordRAM.Instr.accept
end Lax350013.WordRAM.Instr.accept

namespace Lax350013.WordRAM.Instr.add
end Lax350013.WordRAM.Instr.add

namespace Lax350013.WordRAM.Instr.bltz
end Lax350013.WordRAM.Instr.bltz

namespace Lax350013.WordRAM.Instr.load
end Lax350013.WordRAM.Instr.load

namespace Lax350013.WordRAM.Instr.mul
end Lax350013.WordRAM.Instr.mul

namespace Lax350013.WordRAM.Instr.one
end Lax350013.WordRAM.Instr.one

namespace Lax350013.WordRAM.Instr.reject
end Lax350013.WordRAM.Instr.reject

namespace Lax350013.WordRAM.Instr.store
end Lax350013.WordRAM.Instr.store

namespace Lax350013.WordRAM.Instr.sub
end Lax350013.WordRAM.Instr.sub
end

-- Lax350013.PolynomialTime
section
namespace Lax350013.PolynomialTime
end Lax350013.PolynomialTime

namespace Lax350013.PolynomialTime.Problem
end Lax350013.PolynomialTime.Problem
end

-- Lax350013.RAMResources
section
namespace Lax350013.RAMResources.RunsPhases
end Lax350013.RAMResources.RunsPhases

namespace Lax350013.RAMResources.Serves
end Lax350013.RAMResources.Serves

namespace Lax350013.RAMResources

open Finset

open Lax350013.WordRAM

/-- A computational problem on the word RAM. -/
structure Problem where
  /-- The instances. -/
  Inst : Type
  /-- The parameters of an instance on which the word size depends: its sizes. -/
  params : Inst → List ℕ
  /-- The input: the numbers written into the cells 0, 1, 2, … -/
  input : Inst → List ℤ
  /-- `IsAnswer x verdict out`: the verdict, and the numbers `out 0, out 1, …` in the cells right
  after the input, are a correct answer to the instance `x`. -/
  IsAnswer : Inst → Bool → (ℕ → ℤ) → Prop

end Lax350013.RAMResources
end

-- Lax350013.ThinMatrices
section
namespace Lax350013.ThinMatrices

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

/-- A matrix written row by row. -/
def rowMajor {n m : ℕ} (A : Fin n → Fin m → ℤ) : List ℤ :=
  (List.finRange n).flatMap fun i => (List.finRange m).map fun j => A i j

/-- Two matrices `X ∈ ℤ^{N×D}` and `Y ∈ ℤ^{D×N}` with entries of absolute value at most `U`. -/
structure ThinPair where
  /-- The long side. -/
  N : ℕ
  /-- The short side. -/
  D : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The first matrix. -/
  X : Matrix (Fin N) (Fin D) ℤ
  /-- The second matrix. -/
  Y : Matrix (Fin D) (Fin N) ℤ
  /-- The entries of `X` are bounded. -/
  boundX : ∀ i j, |X i j| ≤ (U : ℤ)
  /-- The entries of `Y` are bounded. -/
  boundY : ∀ i j, |Y i j| ≤ (U : ℤ)

/-- Theorem 5: two such matrices and "a set W of [...] positions of an N × N matrix".

NOTE.  The paper does not say how a set is given.  Here it is a list without repetitions, in any
order. -/
structure ThinInstance extends ThinPair where
  /-- The wanted positions. -/
  W : List (Fin N × Fin N)
  /-- No position is listed twice. -/
  nodup : W.Nodup

/-- The input of the matrix problems: `N`, `D`, `|W|`, then further parameters `extra` (none, except
in Theorem 30), then `X`, then `Y`, then the rows `I` of the wanted positions, then their columns
`J`. -/
def ThinInstance.input (x : ThinInstance) (extra : List ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.W.length : ℤ)] ++ extra ++ rowMajor x.X ++ rowMajor x.Y ++
    x.W.map (fun q => (q.1.val : ℤ)) ++ x.W.map (fun q => (q.2.val : ℤ))

end Lax350013.ThinMatrices
end

-- Lax350013.LopsidedTriangles
section
namespace Lax350013.LopsidedTriangles

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

open Lax350013.ThinMatrices

/-- **Definition 13**, the input: "an unweighted undirected tripartite graph with two parts
A and B of n vertices each and a middle part M [...], with arbitrary edges in M × A and M × B.  Let
W ⊆ A × B be the set of edges between A and B."  The bound "of at most D vertices" on the middle
part is `LopInstance.MiddleAtMost`. -/
structure LopInstance (n : ℕ) where
  /-- The middle part `M`. -/
  M : Type
  /-- The middle part is finite. -/
  [fintypeM : Fintype M]
  /-- `adjA a v`: the vertex `a ∈ A` and the middle vertex `v ∈ M` are adjacent. -/
  adjA : Fin n → M → Prop
  /-- `adjB v b`: the middle vertex `v ∈ M` and the vertex `b ∈ B` are adjacent. -/
  adjB : M → Fin n → Prop
  /-- The set `W ⊆ A × B` of edges between `A` and `B`; Section 3.1 calls its elements the query
  pairs. -/
  W : Finset (Fin n × Fin n)

attribute [instance] LopInstance.fintypeM

/-- Definitions 13 and 14: the common neighbors of `a` and `b` in `M`. -/
def LopInstance.commonNeighbors {n : ℕ} (I : LopInstance n) (a b : Fin n) : Set I.M :=
  {v | I.adjA a v ∧ I.adjB v b}

/-- **Definition 14**: "the number of triangles it lies in, that is, the number of common
neighbors of a and b in M". -/
noncomputable def LopInstance.numTriangles {n : ℕ} (I : LopInstance n) (a b : Fin n) : ℕ :=
  (I.commonNeighbors a b).ncard

/-- Footnote 8, Section 3.1: "An instance of #Lop-AE-SparseTri(n,D) asks for the wanted entries of a
thin matrix product of two 0/1 matrices."  This is the instance that two matrices and a set `W` of
positions describe: the middle part is the set of the `D` column indices of `X`, and adjacency means
that the entry is 1. -/
def LopInstance.ofMatrices {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin n) ℤ)
    (W : Finset (Fin n × Fin n)) : LopInstance n where
  M := Fin D
  adjA a v := X a v = 1
  adjB v b := Y v b = 1
  W := W

abbrev ThinInstance := Lax350013.ThinMatrices.ThinInstance

/-- The instance of the lopsided triangle problems that two 0/1 matrices and a list of query pairs
describe.

NOTE.  Definition 13 has "a middle part M of at most D vertices"; here the middle part has exactly
`D` vertices, the columns of `X`.  A smaller middle part is written with zero columns of `X` and
zero rows of `Y`: vertices without edges, which lie in no triangle. -/
def ThinInstance.lop (x : ThinInstance) : LopInstance x.N :=
  LopInstance.ofMatrices x.X x.Y x.W.toFinset

/-- **#Lop-AE-SparseTri** (Definition 14), with the graph given by its two biadjacency matrices: the
`i`-th output cell holds the number of triangles through the `i`-th query pair. -/
def lopCount : Problem where
  Inst := ThinInstance
  params x := [x.N, x.D]
  input x := x.input []
  IsAnswer x verdict out :=
    verdict = true ∧ ∀ (i : ℕ) (h : i < x.W.length),
      out i = (x.lop.numTriangles x.W[i].1 x.W[i].2 : ℤ)

end Lax350013.LopsidedTriangles
end
