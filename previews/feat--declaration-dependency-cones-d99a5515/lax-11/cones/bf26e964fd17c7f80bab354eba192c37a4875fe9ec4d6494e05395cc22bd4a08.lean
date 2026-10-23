-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Basic

-- Lax11.GraphEncoding
section
namespace Lax11
end Lax11

namespace Lax11.GraphEncoding
end Lax11.GraphEncoding

namespace Lax11.GraphEncoding.EncodesGraph
end Lax11.GraphEncoding.EncodesGraph
end

-- Lax808846.Ram
section
namespace Lax808846
end Lax808846

namespace Lax808846.Ram
end Lax808846.Ram

namespace Lax808846.Ram.Instr
end Lax808846.Ram.Instr

namespace Lax808846.Ram.State
end Lax808846.Ram.State

namespace Lax808846.Ram.run
end Lax808846.Ram.run

namespace Lax808846.Ram.Instr.add
end Lax808846.Ram.Instr.add

namespace Lax808846.Ram.Instr.and
end Lax808846.Ram.Instr.and

namespace Lax808846.Ram.Instr.div
end Lax808846.Ram.Instr.div

namespace Lax808846.Ram.Instr.effect
end Lax808846.Ram.Instr.effect

namespace Lax808846.Ram.Instr.halt
end Lax808846.Ram.Instr.halt

namespace Lax808846.Ram.Instr.inputLength
end Lax808846.Ram.Instr.inputLength

namespace Lax808846.Ram.Instr.inputLoad
end Lax808846.Ram.Instr.inputLoad

namespace Lax808846.Ram.Instr.jeof
end Lax808846.Ram.Instr.jeof

namespace Lax808846.Ram.Instr.jump
end Lax808846.Ram.Instr.jump

namespace Lax808846.Ram.Instr.jzero
end Lax808846.Ram.Instr.jzero

namespace Lax808846.Ram.Instr.load
end Lax808846.Ram.Instr.load

namespace Lax808846.Ram.Instr.mul
end Lax808846.Ram.Instr.mul

namespace Lax808846.Ram.Instr.not
end Lax808846.Ram.Instr.not

namespace Lax808846.Ram.Instr.read
end Lax808846.Ram.Instr.read

namespace Lax808846.Ram.Instr.set
end Lax808846.Ram.Instr.set

namespace Lax808846.Ram.Instr.shiftl
end Lax808846.Ram.Instr.shiftl

namespace Lax808846.Ram.Instr.store
end Lax808846.Ram.Instr.store

namespace Lax808846.Ram.Instr.sub
end Lax808846.Ram.Instr.sub

namespace Lax808846.Ram.Instr.write
end Lax808846.Ram.Instr.write
end

-- Lax808846.RamComputes
section
namespace Lax808846.RamComputes
end Lax808846.RamComputes
end

-- Lax11.ConnectedComponents
section
namespace Lax11.ConnectedComponents

open Lax808846.Ram Lax808846.RamComputes Lax11.GraphEncoding

/-- The label of a vertex: the least vertex of its connected
component. -/
noncomputable def label {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  sInf (Fin.val '' {u : Fin n | G.Reachable u v})

/-- The component labelling of a graph: the labels of all vertices, in
vertex order. -/
noncomputable def ccLabels {n : ℕ} (G : SimpleGraph (Fin n)) : List ℕ :=
  List.ofFn (label G)

end Lax11.ConnectedComponents
end
