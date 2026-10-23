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

/-- Section 5.4, Mv-hinted Mv (Definition 5.6 of [vdBNS19]): "Phase 1: N ∈ {0,1}^{n×n} and V ∈
{0,1}^{t×n}.  Phase 2: a vector I ∈ [n]^t of column indices.  Phase 3: an index j, after which the
algorithm outputs N_{[n],I} V_{[t],j}, where N_{[n],I} is the n × t matrix whose k-th column is
column I_k of N." -/
def MvHintedOutput {n t : ℕ} (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t) (Fin n) Bool)
    (I : Fin t → Fin n) (j : Fin n) : Fin n → Bool :=
  fun r => boolMul (N.submatrix id I) V r j

/-- Section 5.4, uMv-hinted uMv (Definition 5.11 of [vdBNS19]): "Phase 1: U ∈ {0,1}^{n×t₁}, N ∈
{0,1}^{n×n}, and V ∈ {0,1}^{t₂×n}.  Phase 2: I ∈ [n]^{t₁}.  Phase 3: J ∈ [n]^{t₂}.  Phase 4: indices
i and j, after which the algorithm outputs (U N_{I,J} V)_{i,j}, where N_{I,J} is the t₁ × t₂
submatrix of N with the rows I and the columns J." -/
def uMvHintedOutput {n t₁ t₂ : ℕ} (U : Matrix (Fin n) (Fin t₁) Bool)
    (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin t₂) (Fin n) Bool) (I : Fin t₁ → Fin n)
    (J : Fin t₂ → Fin n) (i j : Fin n) : Bool :=
  boolMul (boolMul U (N.submatrix I J)) V i j

/-- Section 5.4: "Each conjecture asserts that no algorithm simultaneously beats all of its listed
bounds, for any ε > 0." v-hinted Mv (Conjecture 5.2 of [vdBNS19]): "Bounds conjectured to be
impossible to achieve simultaneously: n^{ω(1,1,τ)-ε} for Phase 2 and n^{1+τ-ε} for Phase 3."

Running times are not defined here, so the conjecture is stated relative to a parameter:
`Achieves a₂ a₃` stands for "some algorithm solves the problem with t = n^τ, with polynomial time in
Phase 1, O(n^{a₂}) time in Phase 2 and O(n^{a₃}) time in Phase 3".  `ω` stands for the number
ω(1,1,τ).  For programs of the word RAM the parameter is `AchievesVHinted τ`.  The exponents of
rectangular matrix multiplication are not defined in Lean: `ω` is an arbitrary real number here, and
the definition says something only together with a condition on it. The statement that the
conjecture fails (`Items.Corollary_40_fail`) is made for every `ω ≥ 2`.

[vdBNS19] words the bounds as lower bounds Ω(n^{x-ε}) on the time of a phase.  That wording implies
the one used here, "not O(n^{x-ε})" (apply it with ε/2), so a refutation of the conjecture in this
form refutes it as worded there.  The same holds for `Conjecture57` and `Conjecture512`. -/
def Conjecture52 (Achieves : ℝ → ℝ → Prop) (ω τ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω - ε) (1 + τ - ε)

/-- Section 5.4, Mv-hinted Mv (Conjecture 5.7 of [vdBNS19]): "n^{ω(1,τ,1)-ε} for Phase 2 and
n^{1+τ-ε} for Phase 3." `Achieves` is as in `Conjecture52`, for the Mv-hinted Mv problem
(`AchievesMvHinted τ`); `ω` stands for ω(1,τ,1). -/
def Conjecture57 (Achieves : ℝ → ℝ → Prop) (ω τ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω - ε) (1 + τ - ε)

/-- Section 5.4, uMv-hinted uMv (Conjecture 5.12 of [vdBNS19]): "n^{ω(1,τ₁,1)-ε} for Phase 2,
n^{ω(τ₂,τ₁,1)-ε} for Phase 3, and n^{τ₁+τ₂-ε} for Phase 4."  `Achieves a₂ a₃ a₄` stands for "some
algorithm solves the problem with t₁ = n^{τ₁} and t₂ = n^{τ₂}, with polynomial time in Phase 1 and
O(n^{a₂}), O(n^{a₃}), O(n^{a₄}) time in Phases 2, 3, 4"; `ω₂` stands for ω(1,τ₁,1) and `ω₃` for
ω(τ₂,τ₁,1).  For programs of the word RAM the parameter is `AchievesUMvHinted τ₁ τ₂`. -/
def Conjecture512 (Achieves : ℝ → ℝ → ℝ → Prop) (ω₂ ω₃ τ₁ τ₂ : ℝ) : Prop :=
  ∀ ε > 0, ¬ Achieves (ω₂ - ε) (ω₃ - ε) (τ₁ + τ₂ - ε)

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

/-- **Mv-hinted Mv** (Section 5.4; Definition 5.6 of [vdBNS19]) with `t = n^τ`, in the same sense.
Phase 1 receives `n`, `t`, the `n × n` matrix `N` and the `t × n` matrix `V`; Phase 2 the `t` column
indices `I`; Phase 3 the index `j`; the output is the `n` entries of `N_{[n],I} V_{[t],j}`. -/
def AchievesMvHinted (τ a₂ a₃ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (N : Matrix (Fin n) (Fin n) Bool) (V : Matrix (Fin (hintSize τ n)) (Fin n) Bool)
      (I : Fin (hintSize τ n) → Fin n) (j : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧
        RunsPhases (fun c off => ∀ r : Fin n, output c off r.val = bit (MvHintedOutput N V I j r))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ n : ℤ)] ++ rowMajor (toInt N) ++ rowMajor (toInt V), s₁),
            (P₂, List.ofFn fun k => ((I k).val : ℤ), s₂), (P₃, [(j.val : ℤ)], s₃)]

/-- **uMv-hinted uMv** (Section 5.4; Definition 5.11 of [vdBNS19]) with `t₁ = n^{τ₁}` and `t₂ =
n^{τ₂}` is solved with polynomial time in Phase 1 and `O(n^{a₂})`, `O(n^{a₃})`, `O(n^{a₄})` time in
Phases 2, 3, 4.  Phase 1 receives `n`, `t₁`, `t₂` and the matrices `U` (`n × t₁`), `N` (`n × n`),
`V` (`t₂ × n`); Phase 2 the `t₁` row indices `I`; Phase 3 the `t₂` column indices `J`; Phase 4 the
indices `i` and `j`; the output is the one entry `(U N_{I,J} V)_{i,j}`. -/
def AchievesUMvHinted (τ₁ τ₂ a₂ a₃ a₄ : ℝ) : Prop :=
  ∃ (P₁ P₂ P₃ P₄ : List Instr) (b : ℕ) (C a₁ : ℝ), ∀ n : ℕ, 1 ≤ n →
    ∀ (U : Matrix (Fin n) (Fin (hintSize τ₁ n)) Bool) (N : Matrix (Fin n) (Fin n) Bool)
      (V : Matrix (Fin (hintSize τ₂ n)) (Fin n) Bool) (I : Fin (hintSize τ₁ n) → Fin n)
      (J : Fin (hintSize τ₂ n) → Fin n)
      (i j : Fin n) (bits : ℕ), Admissible b [n] bits →
      ∃ s₁ s₂ s₃ s₄ : ℕ, Within s₁ C n a₁ ∧ Within s₂ C n a₂ ∧ Within s₃ C n a₃ ∧ Within s₄ C n a₄ ∧
        RunsPhases (fun c off => output c off 0 = bit (uMvHintedOutput U N V I J i j))
          (loadWords bits []) 0
          [(P₁, [(n : ℤ), (hintSize τ₁ n : ℤ), (hintSize τ₂ n : ℤ)] ++ rowMajor (toInt U) ++
              rowMajor (toInt N) ++ rowMajor (toInt V), s₁),
            (P₂, List.ofFn fun k => ((I k).val : ℤ), s₂),
            (P₃, List.ofFn fun k => ((J k).val : ℤ), s₃),
            (P₄, [(i.val : ℤ), (j.val : ℤ)], s₄)]

end Lax350013.HintedMatrixVector
end

-- Lax350013.MatrixParameters
section
namespace Lax350013
end Lax350013

namespace Lax350013.MatrixParameters
end Lax350013.MatrixParameters
end

-- Lax350013.HintedAlgorithms
section
namespace Lax350013.HintedAlgorithms

open Finset

open Lax350013.WordRAM

open Lax350013.RAMResources

open Lax350013.ThinMatrices

open Lax350013.HintedMatrixVector

open Lax350013.MatrixParameters

/-- **Corollary 40**, the running times of its first paragraph (also in **Theorem 4**): for
Conjectures 5.2 and 5.7 and "every 0 < τ < 1/18: Phase 2 takes O(n^{2−0.063τ}) time and Phase 3
takes O(n^{1+0.437τ}) time"; for Conjecture 5.12 and "every 0 < τ₁ < τ₂/18: Phase 3 takes
O(n^{1+τ₂−0.063τ₁}) time and Phase 4 takes O(n^{τ₂+0.437τ₁}) time, with polynomial Phase 1 and a
Phase 2 that only stores I".  (Theorem 4 prints the first two bounds only.)

NOTE.  `τ₂ < 1` is assumed: it is the standing assumption of Section 5.4 ("for constants τ, τ_i ∈
(0,1)").  The words "only stores I" are read as `O(n^{τ₁})` time. -/
def Corollary_40_times : Prop :=
  (∀ τ : ℝ, 0 < τ → τ < 1 / 18 →
    AchievesVHinted τ (2 - 0.063 * τ) (1 + 0.437 * τ) ∧
      AchievesMvHinted τ (2 - 0.063 * τ) (1 + 0.437 * τ)) ∧
  ∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ < τ₂ / 18 → τ₂ < 1 →
    AchievesUMvHinted τ₁ τ₂ τ₁ (1 + τ₂ - 0.063 * τ₁) (τ₂ + 0.437 * τ₁)

/-- **Corollary 40** (also **Theorem 4**), "fail": Conjectures 5.2 and 5.7 of
[vdBNS19], read as statements about programs of this machine, fail for every `0 < τ < τ₀`, and
Conjecture 5.12 fails for every `0 < τ₁ < τ₀ τ₂` (with `τ₂ < 1`), "whatever the value of ω".

The exponents of rectangular matrix multiplication are not defined here.  `ω`, `ω₂`, `ω₃` stand for
`ω(1,1,τ) = ω(1,τ,1)`, `ω(1,τ₁,1)`, `ω(τ₂,τ₁,1)`, and the statement is made for all real numbers
that satisfy the lower bounds of Corollary 40, "ω(1,1,τ) = ω(1,τ,1) ≥ 2 and ω(τ₂,τ₁,1) ≥ 1 + τ₂
because of the input and output sizes"; the bound `2 ≤ ω₂` is the first of these at `τ = τ₁`.  That
the true exponents satisfy these bounds is not proved here. The paper has `τ₀ = 1/18` in the first
paragraph, `ε*` in the second, and `0.1204` in Theorem 4.

NOTE.  `τ₂ < 1` is assumed; see the NOTE at `Corollary_40_times`. -/
def Corollary_40_fail (τ₀ : ℝ) : Prop :=
  (∀ τ ω : ℝ, 0 < τ → τ < τ₀ → 2 ≤ ω →
    ¬ HintedMv.Conjecture52 (AchievesVHinted τ) ω τ ∧
      ¬ HintedMv.Conjecture57 (AchievesMvHinted τ) ω τ) ∧
  ∀ τ₁ τ₂ ω₂ ω₃ : ℝ, 0 < τ₁ → τ₁ < τ₀ * τ₂ → τ₂ < 1 → 2 ≤ ω₂ → 1 + τ₂ ≤ ω₃ →
    ¬ HintedMv.Conjecture512 (AchievesUMvHinted τ₁ τ₂) ω₂ ω₃ τ₁ τ₂

/-- **Theorem 4**: "The v-hinted Mv, Mv-hinted Mv, and uMv-hinted uMv conjectures of
[vdBNS19] [...] are refuted in the regime of thin hints.  For hint dimension t = n^τ with 0 < τ <
1/18, the phase after the hint takes O(n^{2−0.063τ}) time and the phase after the vector
O(n^{1+0.437τ}) time [...]. Correspondingly, the uMv version [...] fails for τ₁ < τ₂/18.  All three
fail, with smaller savings, for every τ < 0.1204 (for the uMv version, τ₁ < 0.1204 τ₂)."  The three
parts follow the sentences of the theorem.  (The first contains also the running times of the uMv
version, which are printed in Corollary 40 only; the second follows from the third.)

NOTE.  For the uMv version `τ₂ < 1` is assumed; see the NOTE at `Corollary_40_times`. -/
def Theorem_4 : Prop :=
  Corollary_40_times ∧ Corollary_40_fail (1 / 18) ∧ Corollary_40_fail 0.1204

end Lax350013.HintedAlgorithms
end
