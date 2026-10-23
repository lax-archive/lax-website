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
namespace Lax350013.ProcedureContracts.Need
end Lax350013.ProcedureContracts.Need

namespace Lax350013.ProcedureContracts.Task
end Lax350013.ProcedureContracts.Task

namespace Lax350013.ProcedureContracts.Need.Ok
end Lax350013.ProcedureContracts.Need.Ok

namespace Lax350013.ProcedureContracts

open Finset

open Lax350013.StructuredPrograms

/-- The cell `b` is not among the `n` cells from address `a`. -/
abbrev Outside (a n b : ℕ) : Prop := b < a ∨ a + n ≤ b

/-- Two regions of the memory, of `n` cells from `a` and of `n'` cells from `a'`, do not meet. -/
abbrev Apart (a n a' n' : ℕ) : Prop := a + n ≤ a' ∨ a' + n' ≤ a

/-- The memory `μ'` agrees with `μ` on every cell that satisfies `K`. -/
def SameOn (K : ℕ → Prop) (μ μ' : ℕ → ℤ) : Prop := ∀ b, K b → μ' b = μ b

/-- No cell below the free pointer has changed, except the `len` cells from `out`. -/
abbrev KeptBut (μ μ' : ℕ → ℤ) (fr out len : ℕ) : Prop :=
  SameOn (fun x => x < fr ∧ Outside out len x) μ μ'

/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]

/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => (x : ℤ))

/-- All members of the list `l` have absolute value at most `U`. -/
def AbsLe (l : List ℤ) (U : ℤ) : Prop := ∀ x ∈ l, |x| ≤ U

/-- A problem with a calling convention and a list of parameters. -/
structure TaskN : Type 1 where
  /-- The instances, as they lie in the memory. -/
  Inst : Type
  /-- The parameters on which time and need depend. -/
  pars : Inst → List ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → (ℕ → ℤ) → ℕ → Prop
  /-- The result and the final memory are right. -/
  Post : Inst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop

end Lax350013.ProcedureContracts
end

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

-- Lax350013.ThreeSUM
section
namespace Lax350013.ThreeSUM
end Lax350013.ThreeSUM
end

-- Lax350013.CallableProblems
section
namespace Lax350013.CallableProblems.GraphInst
end Lax350013.CallableProblems.GraphInst

namespace Lax350013.CallableProblems.MatInst
end Lax350013.CallableProblems.MatInst

namespace Lax350013.CallableProblems.TriInst
end Lax350013.CallableProblems.TriInst

namespace Lax350013.CallableProblems.VecInst
end Lax350013.CallableProblems.VecInst

namespace Lax350013.CallableProblems.walkEnd
end Lax350013.CallableProblems.walkEnd

namespace Lax350013.CallableProblems.GraphInst.Pre
end Lax350013.CallableProblems.GraphInst.Pre

namespace Lax350013.CallableProblems.MatInst.Pre
end Lax350013.CallableProblems.MatInst.Pre

namespace Lax350013.CallableProblems.TriInst.Pre
end Lax350013.CallableProblems.TriInst.Pre

namespace Lax350013.CallableProblems.VecInst.Pre
end Lax350013.CallableProblems.VecInst.Pre

namespace Lax350013.CallableProblems

open Finset

open Lax350013.StructuredPrograms

open Lax350013.ProcedureContracts

namespace TriangleInstance

end TriangleInstance

/-- Matrices `X` (`N × D`) and `Y` (`D × N`), row by row, `w` wanted positions (rows in `WI`,
columns in `WJ`), and the place for `w` answers. -/
structure ThinInst : Type where
  /-- The number of rows of `X` and of columns of `Y`. -/
  N : ℕ
  /-- The number of columns of `X` and of rows of `Y`. -/
  D : ℕ
  /-- The number of wanted positions. -/
  w : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The address of `X`. -/
  x : ℕ
  /-- The address of `Y`. -/
  y : ℕ
  /-- The address of `WI`. -/
  wi : ℕ
  /-- The address of `WJ`. -/
  wj : ℕ
  /-- The address of the answers. -/
  out : ℕ
  /-- The first matrix, row by row. -/
  X : List ℤ
  /-- The second matrix, row by row. -/
  Y : List ℤ
  /-- The rows of the wanted positions. -/
  WI : List ℕ
  /-- The columns of the wanted positions. -/
  WJ : List ℕ

/-- Everything lies below the free pointer, the entries are bounded by `U`, the positions are
distinct positions of an `N × N` matrix, and the place for the answers meets none of the inputs. -/
structure ThinInst.Pre (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  D_pos : 1 ≤ x.D
  U_pos : 1 ≤ x.U
  lenX : x.X.length = x.N * x.D
  lenY : x.Y.length = x.D * x.N
  lenWI : x.WI.length = x.w
  lenWJ : x.WJ.length = x.w
  segX : Seg μ x.x x.X
  segY : Seg μ x.y x.Y
  segWI : SegN μ x.wi x.WI
  segWJ : SegN μ x.wj x.WJ
  leX : AbsLe x.X x.U
  leY : AbsLe x.Y x.U
  ltWI : ∀ i ∈ x.WI, i < x.N
  ltWJ : ∀ j ∈ x.WJ, j < x.N
  nodup : (x.WI.zip x.WJ).Nodup
  belowX : x.x + x.N * x.D ≤ fr
  belowY : x.y + x.D * x.N ≤ fr
  belowWI : x.wi + x.w ≤ fr
  belowWJ : x.wj + x.w ≤ fr
  belowOut : x.out + x.w ≤ fr
  apartX : Apart x.out x.w x.x (x.N * x.D)
  apartY : Apart x.out x.w x.y (x.D * x.N)
  apartWI : Apart x.out x.w x.wi x.w
  apartWJ : Apart x.out x.w x.wj x.w

/-- The entries of both matrices are 0 or 1. -/
def ThinInst.ZeroOne (x : ThinInst) : Prop := (∀ v ∈ x.X, v = 0 ∨ v = 1) ∧ ∀ v ∈ x.Y, v = 0 ∨ v = 1

/-- The entry `(XY)[I, J]`. -/
def thinEntry (N D : ℕ) (X Y : List ℤ) (I J : ℕ) : ℤ :=
  ((List.range D).map fun k => X.getD (I * D + k) 0 * Y.getD (k * N + J) 0).sum

/-- The wanted entries, in the order of the positions. -/
def thinOut (N D : ℕ) (X Y : List ℤ) (WI WJ : List ℕ) : List ℤ :=
  (WI.zip WJ).map fun q => thinEntry N D X Y q.1 q.2

/-- **#Lop-AE-SparseTri** (Definition 14), the graph given by its two biadjacency matrices: the same
call with `U = 1` on matrices of zeros and ones; the answers are the numbers of common
neighbours. -/
def lopCountTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

end Lax350013.CallableProblems
end
