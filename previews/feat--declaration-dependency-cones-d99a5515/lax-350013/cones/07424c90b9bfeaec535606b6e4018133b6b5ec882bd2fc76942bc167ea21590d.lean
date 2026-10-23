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
end Lax350013.PolynomialTime

namespace Lax350013.PolynomialTime.Problem
end Lax350013.PolynomialTime.Problem
end

-- Lax350013.APSP
section
namespace Lax350013.APSP.APSP
end Lax350013.APSP.APSP

namespace Lax350013.APSP

open Lax350013.PolynomialTime

/-- A path and its total weight; it may repeat vertices. -/
inductive Path {n : Nat} (w : Fin n → Fin n → Option Int) : Fin n → Fin n → Int → Prop
  | nil (i : Fin n) : Path w i i 0
  | cons {i j k : Fin n} {d e : Int} : w i j = some d → Path w j k e → Path w i k (d + e)

end Lax350013.APSP
end
