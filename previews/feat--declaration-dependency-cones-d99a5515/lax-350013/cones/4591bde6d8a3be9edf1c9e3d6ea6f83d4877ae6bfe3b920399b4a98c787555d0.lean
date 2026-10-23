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
end Lax350013.PolynomialTime

namespace Lax350013.PolynomialTime.Problem
end Lax350013.PolynomialTime.Problem
end

-- Lax350013.RAMResources
section
namespace Lax350013.RAMResources.Problem
end Lax350013.RAMResources.Problem

namespace Lax350013.RAMResources.Serves
end Lax350013.RAMResources.Serves

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

/-- The output of a function problem: the cells right after the input, read as signed words.
`output c len i` is the number in the `i`-th cell of the memory `c` after an input of `len`
cells. -/
def output {W : Nat} (c : Int → BitVec W) (len : Nat) (i : Nat) : Int :=
  (c ((len : Int) + (i : Int))).toInt

/-- The memory on which a phase starts: the memory `c` with the list `ws` written into the cells
`off, off + 1, …`. -/
def withInput {bits : ℕ} (c : ℤ → BitVec bits) (off : ℕ) (ws : List ℤ) : ℤ → BitVec bits :=
  fun a =>
    if (off : ℤ) ≤ a ∧ a < (off : ℤ) + (ws.length : ℤ) then
      BitVec.ofInt bits (ws.getD (a - (off : ℤ)).toNat 0)
    else c a

/-- The phases of the list, each given by its program, its input and a number of steps, run one
after the other from the memory `c`: every phase starts at its first instruction and accepts within
its number of steps, the inputs are written one after the other from the cell `off` on, and the last
memory, with the address of the first cell after the last input, satisfies `good`.
-/
def RunsPhases {bits : ℕ} (good : (ℤ → BitVec bits) → ℕ → Prop) :
    (ℤ → BitVec bits) → ℕ → List (List Instr × List ℤ × ℕ) → Prop
  | c, off, [] => good c off
  | c, off, (P, ws, s) :: rest =>
    ∃ c' : ℤ → BitVec bits, exec P s 0 (withInput c off ws) = some (true, c') ∧
      RunsPhases good c' (off + ws.length) rest

/-- A number `s` of steps is `O(n^a)` with the constant `C`: `s ≤ C (n^a + 1)`.  For `n ≥ 1` and
`a ≥ 0` the `+ 1` only changes the constant; for `a < 0` the bound means `O(1)`. -/
def Within (s : ℕ) (C : ℝ) (n : ℕ) (a : ℝ) : Prop := (s : ℝ) ≤ C * ((n : ℝ) ^ a + 1)

end Lax350013.RAMResources
end

-- Lax350013.ThinMatrices
section
namespace Lax350013.ThinMatrices.ThinInstance
end Lax350013.ThinMatrices.ThinInstance

namespace Lax350013.ThinMatrices.ThinPair
end Lax350013.ThinMatrices.ThinPair

namespace Lax350013.ThinMatrices

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

/-- A matrix written row by row. -/
def rowMajor {n m : ℕ} (A : Fin n → Fin m → ℤ) : List ℤ :=
  (List.finRange n).flatMap fun i => (List.finRange m).map fun j => A i j

/-- A Boolean as a number. -/
def bit (p : Bool) : ℤ := if p then 1 else 0

end Lax350013.ThinMatrices
end

-- Lax350013.HintedMatrixVector
section
namespace Lax350013.HintedMatrixVector

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

open Lax350013.ThinMatrices

namespace HintedMv

/-- Section 5.4: "All three are over the Boolean semiring".  The product of two Boolean matrices. -/
def boolMul {l m r : ℕ} (M : Matrix (Fin l) (Fin m) Bool) (V : Matrix (Fin m) (Fin r) Bool) :
    Matrix (Fin l) (Fin r) Bool :=
  fun i j => decide (∃ k, M i k = true ∧ V k j = true)

/-- Proof of Corollary 40: "We compute over ℤ with 0/1 matrices".  The 0/1 integer matrix
of a Boolean matrix. -/
def toInt {l m : ℕ} (M : Matrix (Fin l) (Fin m) Bool) : Matrix (Fin l) (Fin m) ℤ :=
  fun i j => if M i j = true then 1 else 0

/-- Section 5.4, v-hinted Mv (Definition 5.1 of [vdBNS19]): "Phase 1: an n × t matrix M.  Phase 2: a
t × n matrix V. Phase 3: an index i, after which the algorithm outputs MV_{[n],i}, the product of M
and column i of V." -/
def vHintedOutput {n t : ℕ} (M : Matrix (Fin n) (Fin t) Bool) (V : Matrix (Fin t) (Fin n) Bool)
    (i : Fin n) : Fin n → Bool :=
  fun r => boolMul M V r i

end HintedMv

open HintedMv

/-- Section 5.4: the hint dimension "t = n^τ".

NOTE.  The paper treats `n^τ` as an integer; here it is rounded down, which keeps what the proof of
Corollary 40 needs, for `n ≥ 1`: `t ≥ 1` if `τ ≥ 0`, and `t^18 ≤ n` if `0 ≤ τ ≤ 1/18`.  The number
`t` is given to the programs in Phase 1, after `n`; they need not compute it. -/
noncomputable def hintSize (τ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ τ⌋₊

/-- **v-hinted Mv** (Section 5.4; Definition 5.1 of [vdBNS19]) with `t = n^τ` is solved with
polynomial time in Phase 1, `O(n^{a₂})` time in Phase 2 and `O(n^{a₃})` time in Phase 3.  Phase 1
receives `n`, `t` and the `n × t` matrix `M`; Phase 2 the `t × n` matrix `V`; Phase 3 the index `i`;
the output is the `n` entries of the Boolean product of `M` and column `i` of `V`. -/
def AchievesVHinted (τ a₂ a₃ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (M : Matrix (Fin n) (Fin (hintSize τ n)) Bool) (V : Matrix (Fin (hintSize τ n)) (Fin n) Bool)
      (i : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧
        RunsPhases (fun c off => ∀ r : Fin n, output c off r.val = bit (vHintedOutput M V i r))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ n : ℤ)] ++ rowMajor (toInt M), s₁),
            (P₂, rowMajor (toInt V), s₂), (P₃, [(i.val : ℤ)], s₃)]

end Lax350013.HintedMatrixVector
end
