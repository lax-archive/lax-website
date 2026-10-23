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
