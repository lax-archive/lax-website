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
namespace Lax350013.StructuredPrograms.Cond
end Lax350013.StructuredPrograms.Cond

namespace Lax350013.StructuredPrograms.Exec
end Lax350013.StructuredPrograms.Exec

namespace Lax350013.StructuredPrograms.Expr
end Lax350013.StructuredPrograms.Expr

namespace Lax350013.StructuredPrograms.Op
end Lax350013.StructuredPrograms.Op

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

namespace Lax350013.StructuredPrograms

open Finset

/-- What a running procedure sees: its local variables and the memory. -/
structure State : Type where
  loc : ℕ → ℤ
  mem : ℕ → ℤ

/-- The limits on a run: largest absolute value of a word, number of memory cells, nesting depth of
calls. -/
structure Limits : Type where
  word : ℤ
  space : ℕ
  depth : ℕ

/-- Everything held in a variable or in a cell fits in a word. -/
def State.Bounded (lim : Limits) (σ : State) : Prop :=
  (∀ x, |σ.loc x| ≤ lim.word) ∧ ∀ a, |σ.mem a| ≤ lim.word

end Lax350013.StructuredPrograms
end
