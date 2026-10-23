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

open Lax350013.WordRAM

/-- `yes`: when to accept (always, if not given). `output`: a condition on the cells after the input, read as signed. -/
structure Problem where
  Instance : Nat → Type
  input {n : Nat} : Instance n → List Int
  yes {n : Nat} : Instance n → Prop := fun _ => True
  output {n : Nat} : Instance n → (Nat → Int) → Prop := fun _ _ => True

def rowByRow {n : Nat} (w : Fin n → Fin n → Int) : List Int :=
  (List.ofFn fun u => List.ofFn fun v => w u v).flatten

end Lax350013.PolynomialTime
end

-- Lax350013.ExactTriangle
section
namespace Lax350013.ExactTriangle
end Lax350013.ExactTriangle

namespace Lax350013.ExactTriangle.ExactTriangle
end Lax350013.ExactTriangle.ExactTriangle
end

-- Lax350013.ZeroWeightClique
section
namespace Lax350013.ZeroWeightClique

open Lax350013.PolynomialTime

open Lax350013.ExactTriangle

/-- `w i j u v`: weight between `u` in part `i` and `v` in part `j`. All `k²` blocks are input; only `i < j` counts. -/
def ZeroWeightKClique (k : Nat) : Problem where
  Instance n := Fin k → Fin k → Fin n → Fin n → Int
  input w := (List.ofFn fun i => (List.ofFn fun j => rowByRow (w i j)).flatten).flatten
  yes {n} w := ∃ v : Fin k → Fin n,
    (List.ofFn fun j => (List.ofFn fun i => if i < j then w i j (v i) (v j) else 0).sum).sum = 0

end Lax350013.ZeroWeightClique
end

-- Lax350013.CliqueOptimization
section
namespace Lax350013.CliqueOptimization

open Finset

/-- The total edge weight of the `k`-clique that has the vertex `v p` in part `p` (Corollary 39):
the sum, over the pairs of parts `p < q`, of the weight between `v p` and `v q`. -/
def cliqueWeight {k n : ℕ} (w : Fin k → Fin k → Fin n → Fin n → ℤ) (v : Fin k → Fin n) : ℤ :=
  ∑ p : Fin k, ∑ q ∈ Finset.univ.filter (fun q : Fin k => p < q), w p q (v p) (v q)

/-- **Min-Weight `k`-Clique** (Corollary 39): accept, and leave in the `p`-th of the `k`
output cells (`p = 0, …, k − 1`) the number, below `n`, of the vertex chosen in part `p`, so that
the `k` vertices form a `k`-clique of minimum total edge weight.  Every such clique is accepted.

NOTE.  The parts have at least one vertex: at `n = 0` there is no clique to output. -/
def MinKClique (k : ℕ) : Lax350013.PolynomialTime.Problem where
  Instance n := {_w : Fin k → Fin k → Fin n → Fin n → ℤ // 1 ≤ n}
  input w := (Lax350013.ZeroWeightClique.ZeroWeightKClique k).input w.1
  output {n} w out := ∃ v : Fin k → Fin n, (∀ p : Fin k, out p.val = ((v p).val : ℤ)) ∧
    ∀ v', cliqueWeight w.1 v ≤ cliqueWeight w.1 v'

end Lax350013.CliqueOptimization
end
