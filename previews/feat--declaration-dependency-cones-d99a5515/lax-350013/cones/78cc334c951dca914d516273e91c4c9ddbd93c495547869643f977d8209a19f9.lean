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
