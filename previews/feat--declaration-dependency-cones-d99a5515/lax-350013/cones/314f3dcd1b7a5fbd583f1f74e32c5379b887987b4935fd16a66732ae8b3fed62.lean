-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d



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
