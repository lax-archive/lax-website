-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Log
import Mathlib.SetTheory.Cardinal.Finite

-- Lax489179.IntegerEncoding
section
namespace Lax489179.IntegerEncoding.decodeOption
end Lax489179.IntegerEncoding.decodeOption

namespace Lax489179.IntegerEncoding

def encodeInt : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def encodeOption : Option ℤ → ℕ
  | none => 0
  | some z => encodeInt z + 1

end Lax489179.IntegerEncoding
end

-- Lax489179.Algorithms
section
namespace Lax489179
end Lax489179

namespace Lax489179.Algorithms
end Lax489179.Algorithms

namespace Lax489179.Algorithms.Mode
end Lax489179.Algorithms.Mode

namespace Lax489179.Algorithms.Mode.deterministic
end Lax489179.Algorithms.Mode.deterministic

namespace Lax489179.Algorithms.Mode.randomized
end Lax489179.Algorithms.Mode.randomized
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

-- Lax489179.WordPrograms
section
namespace Lax489179.WordPrograms
end Lax489179.WordPrograms

namespace Lax489179.WordPrograms.Config
end Lax489179.WordPrograms.Config

namespace Lax489179.WordPrograms.Instruction
end Lax489179.WordPrograms.Instruction

namespace Lax489179.WordPrograms.run
end Lax489179.WordPrograms.run

namespace Lax489179.WordPrograms.step
end Lax489179.WordPrograms.step

namespace Lax489179.WordPrograms.Instruction.coin
end Lax489179.WordPrograms.Instruction.coin

namespace Lax489179.WordPrograms.Instruction.ordinary
end Lax489179.WordPrograms.Instruction.ordinary
end

-- Lax489179.WordTime
section
namespace Lax489179.WordTime

structure Problem where
  Input : Type
  size : Input → ℕ
  encode : Input → List ℕ
  valid : Input → Prop
  correct : Input → List ℕ → Prop

end Lax489179.WordTime
end

-- Lax489179.WeightedAPSP
section
namespace Lax489179.WeightedAPSP

structure Graph where
  vertices : ℕ
  edge : Fin vertices → Fin vertices → Option ℤ

inductive Walk (G : Graph) : Fin G.vertices → Fin G.vertices → ℤ → Prop
  | nil (v : Fin G.vertices) : Walk G v v 0
  | cons {u v z : Fin G.vertices} {a b : ℤ}
      (edge : G.edge u v = some a) (tail : Walk G v z b) : Walk G u z (a + b)

def NoNegativeCycle (G : Graph) : Prop :=
  ∀ v d, Walk G v v d → 0 ≤ d

def BoundedWeights (c : ℕ) (G : Graph) : Prop :=
  ∀ u v z, G.edge u v = some z → z.natAbs ≤ G.vertices ^ c

def Distance (G : Graph) (u v : Fin G.vertices) : Option ℤ → Prop
  | none => ¬ ∃ d, Walk G u v d
  | some d => Walk G u v d ∧ ∀ d', Walk G u v d' → d ≤ d'

def encodeMatrix (n : ℕ) (matrix : Fin n → Fin n → Option ℤ) : List ℕ :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => IntegerEncoding.encodeOption (matrix i j)

def encode (G : Graph) : List ℕ := G.vertices :: encodeMatrix G.vertices G.edge

def Correct (G : Graph) (output : List ℕ) : Prop :=
  ∃ matrix : Fin G.vertices → Fin G.vertices → Option ℤ,
    output = encodeMatrix G.vertices matrix ∧ ∀ u v, Distance G u v (matrix u v)

def problem (c : ℕ) : WordTime.Problem where
  Input := Graph
  size := Graph.vertices
  encode := encode
  valid := fun G => BoundedWeights c G ∧ NoNegativeCycle G
  correct := Correct

end Lax489179.WeightedAPSP
end
