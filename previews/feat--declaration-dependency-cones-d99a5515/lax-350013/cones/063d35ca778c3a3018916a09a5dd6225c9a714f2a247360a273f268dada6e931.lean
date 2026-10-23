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

-- Lax350013.MatrixParameters
section
namespace Lax350013.MatrixParameters

open Finset

/-- Section 2.3.3: "N₀ := 3^{L-m}".  Meant for `m ≤ L`; for `m > L` the subtraction of natural
numbers is cut off at 0 and the value is 1. -/
def N0 (L m : ℕ) : ℕ := 3 ^ (L - m)

/-- Section 2.3.3: "K := binom(L, m)", the number of subsets of `{1, …, L}` of size `m`. -/
def K (L m : ℕ) : ℕ := L.choose m

/-- The decay rate of the `β_d` (Table 1, and Section 4.3): "ρ := 9m / (L - m + 1)". -/
noncomputable def rho (L m : ℕ) : ℝ := 9 * (m : ℝ) / ((L : ℝ) - (m : ℝ) + 1)

/-- The expression inside the `O(·)` of (8) (preprocessing time and space of Theorem 30):
"L m ρ^t/(1 - ρ) N² + N · 10^L / (√K N₀)". -/
noncomputable def cost8 (L m t N : ℕ) : ℝ :=
  (L : ℝ) * (m : ℝ) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2
    + (N : ℝ) * (10 : ℝ) ^ L / (Real.sqrt (K L m : ℝ) * (N0 L m : ℝ))

/-- Section 4.4: "let H(x) := -x ln x - (1 - x) ln(1 - x) be the entropy function (with natural
logarithms)". (Lean's `Real.log 0 = 0` gives `H(0) = H(1) = 0`, the usual convention.) -/
noncomputable def entropy (θ : ℝ) : ℝ := -θ * Real.log θ - (1 - θ) * Real.log (1 - θ)

/-- The denominator of equation (11), which the paper calls `ln Λ`:
`c ln 10 - (1/2) c H(1/c) - (c - 1) ln 3 + γ ln 4`, where "Λ := 10^c e^{-(1/2) c H(1/c)} 3^{-(c-1)}
4^γ" (Section 4.4). -/
noncomputable def lnΛ (c γ : ℝ) : ℝ :=
  c * Real.log 10 - (1 / 2) * c * entropy (1 / c) - (c - 1) * Real.log 3 + γ * Real.log 4

/-- Equation (11): "R_c(γ) := ln 4 / ln Λ". -/
noncomputable def Rc (c γ : ℝ) : ℝ := Real.log 4 / lnΛ c γ

/-- Corollary 31: "ρ_c := 9/(c - 1)". -/
noncomputable def rhoC (c : ℝ) : ℝ := 9 / (c - 1)

/-- Corollary 31: "γ := θ ln(1/ρ_c) / ln 4". -/
noncomputable def gammaOf (c θ : ℝ) : ℝ := θ * Real.log (1 / rhoC c) / Real.log 4

/-- Corollary 31: "q := (H(θ) + θ ln 9) / ln 4". -/
noncomputable def qOf (θ : ℝ) : ℝ := (entropy θ + θ * Real.log 9) / Real.log 4

end Lax350013.MatrixParameters
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

/-- The conclusion of Theorem 24 and Corollary 31: there is a data structure for the inputs with
`2 ≤ D ≤ N^ε` with preprocessing in `O(N² log² D/D^γ)` time and space and queries in
`O(D^q log D)` time. -/
def HasDataStructure (ε γ q : ℝ) : Prop :=
  ∀ c₀ : ℕ, ∃ (P Q : List Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
    IsDataStructure P Q qI qJ qOut b [] (thinDom 2 ε c₀)
      (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ))
      (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ))
      (fun x => C * ((x.D : ℝ) ^ q * Real.log x.D))

/-- **Corollary 31**: "Let c > 10 and 0 < θ < 0.9, let ρ_c := 9/(c−1), and let γ := θ
ln(1/ρ_c)/ln 4 > 0 and q := (H(θ) + θ ln 9)/ln 4.  Given as input matrices X ∈ ℤ^{N×D} and Y ∈
ℤ^{D×N} whose entries are integers of absolute value at most N^{O(1)}, where 2 ≤ D ≤ N^ε and ε <
R_c(γ), with R_c as in (11), we can preprocess them deterministically in O(N² log² D/D^γ) time and
space, after which any single entry (XY)[I,J] can be computed deterministically in O(D^q log D)
time.  The constants hidden in the O(·) depend on c, θ, and ε." -/
def Corollary_31 : Prop :=
  ∀ c θ ε : ℝ, 10 < c → 0 < θ → θ < 0.9 → ε < Rc c (gammaOf c θ) →
    HasDataStructure ε (gammaOf c θ) (qOf θ)

end Lax350013.MatrixTradeoffs
end
