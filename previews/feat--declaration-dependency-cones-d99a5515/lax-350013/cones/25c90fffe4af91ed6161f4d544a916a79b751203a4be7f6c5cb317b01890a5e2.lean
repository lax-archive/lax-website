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

open Lax350013.WordRAM

/-- `yes`: when to accept (always, if not given). `output`: a condition on the cells after the input, read as signed. -/
structure Problem where
  Instance : Nat → Type
  input {n : Nat} : Instance n → List Int
  yes {n : Nat} : Instance n → Prop := fun _ => True
  output {n : Nat} : Instance n → (Nat → Int) → Prop := fun _ _ => True

/-- One run: with `n` in cell 0 and the input after it, `P` halts within `t` steps with the right verdict and output. -/
def Problem.SolvedBy (Q : Problem) {n : Nat} (x : Q.Instance n) (P : List Instr) (W t : Nat) : Prop :=
  ∃ verdict m, exec P t 0 (loadWords W ((n : Int) :: Q.input x)) = some (verdict, m) ∧
    (verdict = true ↔ Q.yes x) ∧ Q.output x fun a => (m (1 + (Q.input x).length + a : Nat)).toInt

def rowByRow {n : Nat} (w : Fin n → Fin n → Int) : List Int :=
  (List.ofFn fun u => List.ofFn fun v => w u v).flatten

end Lax350013.PolynomialTime
end

-- Lax350013.APSP
section
namespace Lax350013.APSP

open Lax350013.PolynomialTime

/-- A path and its total weight; it may repeat vertices. -/
inductive Path {n : Nat} (w : Fin n → Fin n → Option Int) : Fin n → Fin n → Int → Prop
  | nil (i : Fin n) : Path w i i 0
  | cons {i j k : Fin n} {d e : Int} : w i j = some d → Path w j k e → Path w i k (d + e)

/-- Input: the 0/1 matrix of the edges, then the weights, with 0 for no edge. Output, two cells for each `(i, j)`: 1 if
there is a path, else 0; then the distance. -/
def APSP : Problem where
  Instance n := {w : Fin n → Fin n → Option Int // ∀ i d, Path w i i d → 0 ≤ d}
  input := fun ⟨w, _⟩ => rowByRow (fun i j => if (w i j).isSome then 1 else 0) ++ rowByRow fun i j => (w i j).getD 0
  output := fun {n} ⟨w, _⟩ out => ∀ i j : Fin n,
    let flag := out (2 * (i.val * n + j.val))
    let dist := out (2 * (i.val * n + j.val) + 1)
    (flag = 1 ∧ Path w i j dist ∧ ∀ e, Path w i j e → dist ≤ e) ∨ (flag = 0 ∧ ∀ e, ¬ Path w i j e)

end Lax350013.APSP
end

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

-- Lax350013.ThreeSUM
section
namespace Lax350013.ThreeSUM

open Lax350013.PolynomialTime

/-- Section 1: «Given n numbers, decide whether three of them sum to 0». Three different positions. -/
def ThreeSum : Problem where
  Instance n := Fin n → Int
  input x := List.ofFn x
  yes x := ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0

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

-- Lax350013.ExactTriangle
section
namespace Lax350013.ExactTriangle

open Lax350013.PolynomialTime

/-- Section 3.2: «S(a, b, c) := w(a, b) + w(b, c) + w(a, c). A zero triangle is a triangle … with S(a, b, c) = 0». -/
def ExactTriangle : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (wAB, wBC, wAC) => rowByRow wAB ++ rowByRow wBC ++ rowByRow wAC
  yes := fun (wAB, wBC, wAC) => ∃ a b c, wAB a b + wBC b c + wAC a c = 0

end Lax350013.ExactTriangle
end

-- Lax350013.MinPlusProduct
section
namespace Lax350013.MinPlusProduct

open Lax350013.PolynomialTime

/-- Output, row by row: entry `(i, j)` is the least of the sums `A i k + B k j`. -/
def MinPlusProduct : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (A, B) => rowByRow A ++ rowByRow B
  output := fun {n} (A, B) out => ∀ i j : Fin n,
    (∃ k, out (i.val * n + j.val) = A i k + B k j) ∧ ∀ k, out (i.val * n + j.val) ≤ A i k + B k j

end Lax350013.MinPlusProduct
end

-- Lax350013.RAMResources
section
namespace Lax350013.RAMResources.Problem
end Lax350013.RAMResources.Problem

namespace Lax350013.RAMResources.RunsPhases
end Lax350013.RAMResources.RunsPhases

namespace Lax350013.RAMResources.Serves
end Lax350013.RAMResources.Serves

namespace Lax350013.RAMResources

open Finset

open Lax350013.WordRAM

/-- The program `P` with slope `b` solves the problem `Q` within `T(n)` steps when all numbers are
integers of absolute value at most `n^κ`.  This is what `Lax350013.PolynomialTime.Problem.SolvedInTime` asks of
the runs of `P`, for a real bound `T`: on every such instance, of any size `n`, and at every word
size of at least `b (⌊log₂ n⌋ + 1)` bits, `P` halts within `T(n)` steps with the right verdict and
output (`Lax350013.PolynomialTime.Problem.SolvedBy`).

NOTE.  As in `Lax350013.PolynomialTime.Problem.SolvedInTime`, the bound speaks of every number of the input
list.  Where the input contains an adjacency matrix, its entries 1 count too; `n^κ` is at least 1 as
soon as there is a vertex. -/
def SolvesWithin (Q : Lax350013.PolynomialTime.Problem) (κ : ℕ) (P : List Instr) (b : ℕ) (T : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Q.Instance n), (∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ) → ∀ W ≥ b * (Nat.log2 n + 1),
    ∃ t : ℕ, (t : ℝ) ≤ T n ∧ Q.SolvedBy x P W t

/-- The problem `Q`, a value of `Lax350013.PolynomialTime.Problem`, is solved by a deterministic algorithm in
`O(n^a (log n)^e)` time when all numbers are integers of absolute value at most `n^κ`: there are a
program, a slope and a constant `C` such that the program solves `Q` within `C (n^a (log n)^e + 1)`
steps.  (For `a ≥ 0` the `+ 1` matters only at `n ≤ 1`, where `n^a (log n)^e` may be 0.) -/
def SolvedInTimeAt (Q : Lax350013.PolynomialTime.Problem) (κ : ℕ) (a : ℝ) (e : ℕ) : Prop :=
  ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    SolvesWithin Q κ P b fun n => C * ((n : ℝ) ^ a * Real.log n ^ e + 1)

/-- The same for every constant `κ`: "all numbers in the input are integers of absolute value
n^{O(1)}" (Theorem 2).  The program, the slope and the constant may depend on `κ`.

NOTE.  `κ` is the paper's ν.  Where the paper has ν ≥ 1 (Theorem 19, Corollary 39), `κ = 0` is
included here. -/
def SolvedInTime (Q : Lax350013.PolynomialTime.Problem) (a : ℝ) (e : ℕ) : Prop :=
  ∀ κ : ℕ, SolvedInTimeAt Q κ a e

end Lax350013.RAMResources
end

-- Lax350013.IntegerAlgorithmBounds
section
namespace Lax350013.IntegerAlgorithmBounds

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

/-- **Theorem 2**, the deterministic half: "On a word RAM with O(log n)-bit words,
deterministic algorithms solve the following problems, where all numbers in the input are integers
of absolute value n^{O(1)}: Exact Triangle on n-vertex graphs in O(n^{2.9983}) time, APSP on
directed n-vertex graphs with no negative cycles in O(n^{2.9995}) time, the (min,+)-product of two
n × n matrices in O(n^{2.9995}) time, and 3SUM on n numbers in O(n^{1.9992}) time."  (For APSP and
the (min,+)-product, Theorem 22 prints the smaller exponent 2.99942: `Theorem_22_second`.)

NOTE.  Here Exact Triangle has the tripartite form of Section 3.2, with `n` vertices per part; for
`n`-vertex graphs see `Theorem_2_graphs`. -/
def Theorem_2 : Prop :=
  SolvedInTime Lax350013.ExactTriangle.ExactTriangle 2.9983 0 ∧
  SolvedInTime Lax350013.APSP.APSP 2.9995 0 ∧
  SolvedInTime Lax350013.MinPlusProduct.MinPlusProduct 2.9995 0 ∧
  SolvedInTime Lax350013.ThreeSUM.ThreeSum 1.9992 0

end Lax350013.IntegerAlgorithmBounds
end
