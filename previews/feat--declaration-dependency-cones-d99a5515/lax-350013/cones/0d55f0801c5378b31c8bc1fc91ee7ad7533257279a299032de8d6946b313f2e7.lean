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

-- Lax350013.StructuredPrograms
section
namespace Lax350013
end Lax350013

namespace Lax350013.StructuredPrograms
end Lax350013.StructuredPrograms

namespace Lax350013.StructuredPrograms.Cond
end Lax350013.StructuredPrograms.Cond

namespace Lax350013.StructuredPrograms.Exec
end Lax350013.StructuredPrograms.Exec

namespace Lax350013.StructuredPrograms.Expr
end Lax350013.StructuredPrograms.Expr

namespace Lax350013.StructuredPrograms.Limits
end Lax350013.StructuredPrograms.Limits

namespace Lax350013.StructuredPrograms.Op
end Lax350013.StructuredPrograms.Op

namespace Lax350013.StructuredPrograms.State
end Lax350013.StructuredPrograms.State

namespace Lax350013.StructuredPrograms.Stmt
end Lax350013.StructuredPrograms.Stmt

namespace Lax350013.StructuredPrograms.Cond.eq
end Lax350013.StructuredPrograms.Cond.eq

namespace Lax350013.StructuredPrograms.Cond.lt
end Lax350013.StructuredPrograms.Cond.lt

namespace Lax350013.StructuredPrograms.Expr.const
end Lax350013.StructuredPrograms.Expr.const

namespace Lax350013.StructuredPrograms.Expr.load
end Lax350013.StructuredPrograms.Expr.load

namespace Lax350013.StructuredPrograms.Expr.op
end Lax350013.StructuredPrograms.Expr.op

namespace Lax350013.StructuredPrograms.Expr.var
end Lax350013.StructuredPrograms.Expr.var

namespace Lax350013.StructuredPrograms.Op.add
end Lax350013.StructuredPrograms.Op.add

namespace Lax350013.StructuredPrograms.Op.eval
end Lax350013.StructuredPrograms.Op.eval

namespace Lax350013.StructuredPrograms.Op.mul
end Lax350013.StructuredPrograms.Op.mul

namespace Lax350013.StructuredPrograms.Op.sub
end Lax350013.StructuredPrograms.Op.sub

namespace Lax350013.StructuredPrograms.Stmt.call
end Lax350013.StructuredPrograms.Stmt.call

namespace Lax350013.StructuredPrograms.Stmt.ite
end Lax350013.StructuredPrograms.Stmt.ite

namespace Lax350013.StructuredPrograms.Stmt.seq
end Lax350013.StructuredPrograms.Stmt.seq

namespace Lax350013.StructuredPrograms.Stmt.set
end Lax350013.StructuredPrograms.Stmt.set

namespace Lax350013.StructuredPrograms.Stmt.skip
end Lax350013.StructuredPrograms.Stmt.skip

namespace Lax350013.StructuredPrograms.Stmt.store
end Lax350013.StructuredPrograms.Stmt.store

namespace Lax350013.StructuredPrograms.Stmt.while
end Lax350013.StructuredPrograms.Stmt.while
end

-- Lax350013.ProcedureContracts
section
namespace Lax350013.ProcedureContracts
end Lax350013.ProcedureContracts

namespace Lax350013.ProcedureContracts.Need
end Lax350013.ProcedureContracts.Need

namespace Lax350013.ProcedureContracts.Task
end Lax350013.ProcedureContracts.Task

namespace Lax350013.ProcedureContracts.TaskN
end Lax350013.ProcedureContracts.TaskN

namespace Lax350013.ProcedureContracts.Need.Ok
end Lax350013.ProcedureContracts.Need.Ok
end

-- Lax350013.WordRAM
section
namespace Lax350013.WordRAM

/-- `i j k` name cells, `l` a position in the program, `[i]` is the word in cell `i`. The only constant is 1. -/
inductive Instr where
  | one (i : Int)             -- [i] := 1
  | add (i j k : Int)         -- [i] := [j] + [k]
  | sub (i j k : Int)         -- [i] := [j] - [k]
  | mul (i j k : Int)         -- [i] := [j] * [k]
  | load (i j : Int)          -- [i] := [[j]]
  | store (i j : Int)         -- [[i]] := [j]
  | bltz (i : Int) (l : Nat)  -- if [i] < 0, go to position l
  | accept
  | reject

/-- The verdict and the final memory, if `P`, run from position `pc` on memory `m`, halts within `t` steps, the halting
step counted; past its end `P` rejects. Addresses are read signed; `bltz` jumps on a negative word; `write` runs on. -/
def exec {W : Nat} (P : List Instr) : (t pc : Nat) → (m : Int → BitVec W) → Option (Bool × (Int → BitVec W))
  | 0, _, _ => none
  | t + 1, pc, m =>
    let write (i : Int) (v : BitVec W) := exec P t (pc + 1) fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => write i 1
    | .add i j k => write i (m j + m k)
    | .sub i j k => write i (m j - m k)
    | .mul i j k => write i (m j * m k)
    | .load i j => write i (m (m j).toInt)
    | .store i j => write (m i).toInt (m j)
    | .bltz i l => exec P t (if (m i).toInt < 0 then l else pc + 1) m
    | .accept => some (true, m)
    | .reject => some (false, m)

/-- The memory at the start: `ws` in cells 0, 1, 2, …, and 0 in every other cell. -/
def loadWords (W : Nat) (ws : List Int) : Int → BitVec W :=
  fun a => if a < 0 then 0 else BitVec.ofInt W (ws.getD a.toNat 0)

end Lax350013.WordRAM
end

-- Lax350013.PolynomialTime
section
namespace Lax350013.PolynomialTime
end Lax350013.PolynomialTime

namespace Lax350013.PolynomialTime.Problem
end Lax350013.PolynomialTime.Problem
end

-- Lax350013.ThreeSUM
section
namespace Lax350013.ThreeSUM
end Lax350013.ThreeSUM
end

-- Lax350013.CallableProblems
section
namespace Lax350013.CallableProblems
end Lax350013.CallableProblems

namespace Lax350013.CallableProblems.GraphInst
end Lax350013.CallableProblems.GraphInst

namespace Lax350013.CallableProblems.MatInst
end Lax350013.CallableProblems.MatInst

namespace Lax350013.CallableProblems.ThinInst
end Lax350013.CallableProblems.ThinInst

namespace Lax350013.CallableProblems.TriInst
end Lax350013.CallableProblems.TriInst

namespace Lax350013.CallableProblems.TriangleInstance
end Lax350013.CallableProblems.TriangleInstance

namespace Lax350013.CallableProblems.VecInst
end Lax350013.CallableProblems.VecInst

namespace Lax350013.CallableProblems.walkEnd
end Lax350013.CallableProblems.walkEnd

namespace Lax350013.CallableProblems.GraphInst.Pre
end Lax350013.CallableProblems.GraphInst.Pre

namespace Lax350013.CallableProblems.MatInst.Pre
end Lax350013.CallableProblems.MatInst.Pre

namespace Lax350013.CallableProblems.ThinInst.Pre
end Lax350013.CallableProblems.ThinInst.Pre

namespace Lax350013.CallableProblems.TriInst.Pre
end Lax350013.CallableProblems.TriInst.Pre

namespace Lax350013.CallableProblems.VecInst.Pre
end Lax350013.CallableProblems.VecInst.Pre
end

-- Lax350013.CallableAlgorithms
section
namespace Lax350013.CallableAlgorithms
end Lax350013.CallableAlgorithms

namespace Lax350013.CallableAlgorithms.Claim
end Lax350013.CallableAlgorithms.Claim

namespace Lax350013.CallableAlgorithms.Closure
end Lax350013.CallableAlgorithms.Closure

namespace Lax350013.CallableAlgorithms.DetTimeModel
end Lax350013.CallableAlgorithms.DetTimeModel
end

-- Lax350013.MatrixParameters
section
namespace Lax350013
end Lax350013

namespace Lax350013.MatrixParameters
end Lax350013.MatrixParameters
end

-- Lax350013.RAMResources
section
namespace Lax350013.RAMResources.Problem
end Lax350013.RAMResources.Problem

namespace Lax350013.RAMResources.RunsPhases
end Lax350013.RAMResources.RunsPhases

namespace Lax350013.RAMResources

open Finset

open Lax350013.WordRAM

/-- The word size `W` is admissible against the slope `b` for an input with the parameters `params`
(its sizes): `W` is at least `b · (⌊log₂ p₁⌋ + ⌊log₂ p₂⌋ + … + 1)`.  If every parameter is at most a
fixed power of the size `n`, the smallest admissible word size is a constant times `log n`: "O(log
n)-bit words".  A statement fixes only the slope `b`, together with the program, and the program has
to work, within the same bound on the number of steps, at every admissible word size. -/
def Admissible (b : Nat) (params : List Nat) (W : Nat) : Prop :=
  b * ((params.map Nat.log2).sum + 1) ≤ W

/-- The memory on which a query starts: the memory `c`, left behind by the preprocessing or by the
previous query, with the row `I` and the column `J` written into the two query cells `qI` and
`qJ`. -/
def withQuery {bits : ℕ} (c : ℤ → BitVec bits) (qI qJ : ℤ) (I J : ℕ) : ℤ → BitVec bits :=
  fun a => if a = qI then BitVec.ofInt bits I else if a = qJ then BitVec.ofInt bits J else c a

/-- The query program `Q` serves the queries of the list one after the other, starting from the
memory `c`: each run starts at the first instruction, accepts within `tq` steps and leaves the right
entry in the cell `qOut`; the next query starts from the memory that this run leaves. -/
def Serves {bits : ℕ} (Q : List Instr) (qI qJ qOut : ℤ) (tq : ℕ) (entry : ℕ → ℕ → ℤ) :
    (ℤ → BitVec bits) → List (ℕ × ℕ) → Prop
  | _, [] => True
  | c, q :: rest =>
    ∃ c' : ℤ → BitVec bits, exec Q tq 0 (withQuery c qI qJ q.1 q.2) = some (true, c') ∧
      (c' qOut).toInt = entry q.1 q.2 ∧ Serves Q qI qJ qOut tq entry c' rest

end Lax350013.RAMResources
end

-- Lax350013.ThinMatrices
section
namespace Lax350013.ThinMatrices.ThinInstance
end Lax350013.ThinMatrices.ThinInstance

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

/-- The input of the preprocessing: `N`, `D`, further parameters `extra` (none, except in
Theorem 30), then `X`, then `Y`.  The list `extra` is fixed before the instance. -/
def ThinPair.input (x : ThinPair) (extra : List ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ)] ++ extra ++ rowMajor x.X ++ rowMajor x.Y

/-- **A data structure for the entries of a thin matrix product** (Theorem 30, Corollary 26): "After
preprocessing X and Y [...], the data structure answers a query for any single entry of XY, not
known in advance" (Section 4).

`P` is the preprocessing program, `Q` the query program, `qI`, `qJ`, `qOut` the three cells through
which queries are put and answered; all of them, and the slope `b`, are fixed before the instance.
On every instance in `dom` and at every admissible word size:

* time: the preprocessing accepts within `Tp x` steps;
* space: it leaves unchanged every cell `a` with `a < -Sp x` or `a > len + Sp x`, where the input
  occupies the cells 0 to `len - 1` (so the cells of the input are not counted);
* queries: then every sequence of queries `(I, J)` with `I, J < N` is served, each query within
  `Tq x` steps.  A query starts on the memory left behind; nothing is reset for it.

NOTE.  The paper says "time and space" and does not define space.  Here space is the extent of the
memory in which the preprocessing leaves the data structure, not the number of cells written, which
is at most the time anyway; a structure that is scattered over a large range of addresses does not
count as small.  Cells that the preprocessing restores, and cells that the queries write, are not
constrained. -/
def IsDataStructure (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (extra : List ℤ)
    (dom : ThinPair → Prop) (Tp Sp Tq : ThinPair → ℝ) : Prop :=
  ∀ x : ThinPair, dom x → ∀ bits : ℕ, Admissible b [x.N, x.D] bits →
    ∃ (tp tq : ℕ) (c : ℤ → BitVec bits), (tp : ℝ) ≤ Tp x ∧ (tq : ℝ) ≤ Tq x ∧
      exec P tp 0 (loadWords bits (x.input extra)) = some (true, c) ∧
      (∀ a : ℤ, ((a : ℝ) < -Sp x ∨ ((x.input extra).length : ℝ) + Sp x < (a : ℝ)) →
        c a = loadWords bits (x.input extra) a) ∧
      ∀ queries : List (ℕ × ℕ), (∀ q ∈ queries, q.1 < x.N ∧ q.2 < x.N) →
        Serves Q qI qJ qOut tq
          (fun I J => if h : I < x.N ∧ J < x.N then (x.X * x.Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0) c queries

end Lax350013.ThinMatrices
end

-- Lax350013.MatrixTradeoffs
section
namespace Lax350013.MatrixTradeoffs

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

open Lax350013.ThinMatrices

open Lax350013.MatrixParameters

/-- The hypotheses on the input in Corollaries 31 and 32 and Theorems 24 and 25: "where 2 ≤ D ≤
N^ε", with entries "of absolute value at most N^{O(1)}".  `lo` is the lower bound on `D`, which is 2
there.  (`N ≥ 1` follows if `lo = 2`; for `lo = 1` it excludes `N = 0`, `D = 1`, `ε = 0`, where the
bounds with the factor `N²` would be 0.) -/
def thinDom (lo : ℕ) (ε : ℝ) (c₀ : ℕ) (x : ThinPair) : Prop :=
  1 ≤ x.N ∧ lo ≤ x.D ∧ (x.D : ℝ) ≤ (x.N : ℝ) ^ ε ∧ x.U = x.N ^ c₀

/-- For every `ε < ε₀` and every `q > 0` there is a `γ > 0` such that, whenever `D ≤ N^ε`, the pair
can be preprocessed in `O(N²/D^γ)` time (and space), after which any single entry can be computed in
`O(D^q)` time.  The paper has this sentence with `ε₀ = 0.1204` (Theorem 3).

NOTE.  The paper states no lower bound on `D` and `N` here, and speaks of time only; `D ≥ 1` and
`N ≥ 1` are assumed, and the space is bounded like the time.  Theorem 24 has logarithmic factors and
assumes `D ≥ 2`; on the step from there Section 4.1 says: "The logarithmic factors in both theorems
can be removed by halving γ and applying Theorem 24 with q/2 in place of q; for D = 1 the bounds are
trivial." -/
def DataStructureBelow (ε₀ : ℝ) : Prop :=
  ∀ ε q : ℝ, ε < ε₀ → 0 < q → ∃ γ : ℝ, 0 < γ ∧
    ∀ c₀ : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
      IsDataStructure P Q qI qJ qOut b [] (thinDom 1 ε c₀)
        (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ γ))
        (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ γ))
        (fun x => C * (x.D : ℝ) ^ q)

end Lax350013.MatrixTradeoffs
end

-- Lax350013.MatrixPreprocessing
section
namespace Lax350013.MatrixPreprocessing

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

open Lax350013.ThinMatrices

open Lax350013.MatrixParameters

open Lax350013.MatrixTradeoffs

/-- **Corollary 26**, first two sentences: "Let N ≥ D^18, and let X ∈ ℤ^{N×D} and Y ∈ ℤ^{D×N}
have entries of absolute value at most N^{O(1)}.  We can preprocess them deterministically in
O(N²/D^{0.063}) time and space, after which any single entry (XY)[I,J] can be computed
deterministically in O(D^{0.437}) time."

NOTE.  The paper states no lower bound on `D`; `D ≥ 1` is assumed (for `D = 0` the bound
`O(D^{0.437})` would be 0 steps). -/
def Corollary_26 : Prop :=
  ∀ c : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
    IsDataStructure P Q qI qJ qOut b [] (fun x => 1 ≤ x.D ∧ x.D ^ 18 ≤ x.N ∧ x.U = x.N ^ c)
      (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))
      (fun x => C * ((x.N : ℝ) ^ 2 / (x.D : ℝ) ^ (0.063 : ℝ)))
      (fun x => C * (x.D : ℝ) ^ (0.437 : ℝ))

/-- **Theorem 3**: "Let N ≥ D^18, and let X ∈ ℤ^{N×D}, Y ∈ ℤ^{D×N} have entries of absolute
value N^{O(1)}. The pair (X,Y) can be preprocessed deterministically in O(N²/D^{0.063}) time [...].
After this, any single entry (XY)[I,J] can be computed deterministically in O(D^{0.437}) time [...].
More generally, for every ε < 0.1204 and every q > 0 there is a γ > 0 such that, whenever D ≤ N^ε,
the pair can be preprocessed in O(N²/D^γ) time, after which any single entry can be computed in
O(D^q) time."  The first part is `Corollary_26`.

NOTE.  The departures are those of the two definitions: `D ≥ 1` in the first part; `D ≥ 1` and
`N ≥ 1` in the second; and in both the space is bounded like the time, while the theorem speaks of
time only. -/
def Theorem_3 : Prop :=
  Corollary_26 ∧ DataStructureBelow 0.1204

end Lax350013.MatrixPreprocessing
end
