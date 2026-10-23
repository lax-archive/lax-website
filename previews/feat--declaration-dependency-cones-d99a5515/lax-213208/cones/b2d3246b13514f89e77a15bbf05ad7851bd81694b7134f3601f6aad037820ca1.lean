-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.DeriveFintype

-- Lax560851.StructuralPresentation
section
namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

namespace Presentation

/-- Distinct values have distinct structural representations. -/
def Faithful {α : Type u} (P : Presentation α) : Prop :=
  Function.Injective P.toRaw

end Presentation

end Lax560851.StructuralPresentation
end

-- Lax560851.WordArena
section
namespace Lax560851.WordArena.WordImage.ChildAddress
end Lax560851.WordArena.WordImage.ChildAddress

namespace Lax560851.WordArena.WordImage.ReachableFrom
end Lax560851.WordArena.WordImage.ReachableFrom

namespace Lax560851.WordArena.WordImage.Represents
end Lax560851.WordArena.WordImage.Represents

namespace Lax560851.WordArena

open Lax560851.StructuralPresentation

universe u

/-- A finite array of unbounded natural-number words. -/
abbrev WordMemory := Array Nat

/-- A closed word array together with its distinguished root address. -/
structure WordImage where
  memory : WordMemory
  root : Nat
  deriving DecidableEq

namespace WordImage

/-- The distinguished Lax808846 input tape: root, followed by all arena words. -/
def toInput (I : WordImage) : List Nat := I.root :: I.memory.toList

/-- Tag of a natural-payload block. -/
def natTag : Nat := 0

/-- Tag of a binary-pair block. -/
def pairTag : Nat := 1

end WordImage

/-- Append the postorder arena of a raw value and return its root address. -/
def encodeInto : Raw → WordMemory → WordMemory × Nat
  | .nat payload, memory =>
      let address := memory.size
      (memory.push WordImage.natTag |>.push payload |>.push 0, address)
  | .pair left right, memory =>
      let (memory, leftAddress) := encodeInto left memory
      let (memory, rightAddress) := encodeInto right memory
      let address := memory.size
      (memory.push WordImage.pairTag |>.push leftAddress |>.push rightAddress, address)

/-- Distinguished closed postorder arena of a structural value. -/
def encodeRaw (raw : Raw) : WordImage :=
  let (memory, root) := encodeInto raw #[]
  { memory, root }

/-- Distinguished arena of a value through a named structural presentation. -/
def encode {α : Type u} (P : Presentation α) (x : α) : WordImage :=
  encodeRaw (P.toRaw x)

end Lax560851.WordArena
end

-- Lax759944.BinaryWordEncoding
section
set_option backward.isDefEq.respectTransparency false

namespace Lax759944.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

/-- Encode one natural number, including the separator which begins it. -/
def encodeNat (n : ℕ) : List Symbol :=
  .separator :: n.bits.map (fun b => if b then .one else .zero)

/-- The canonical binary encoding of a finite list of natural numbers. -/
def encode (x : List ℕ) : List Symbol :=
  x.flatMap encodeNat

/-- The bit-size of a finite list of natural numbers. -/
def bitSize (x : List ℕ) : ℕ :=
  (encode x).length

end Lax759944.BinaryWordEncoding
end

-- Lax213208.OptimizationProblem
section
namespace Lax213208.OptimizationProblem

open scoped NNReal

open Lax560851.StructuralPresentation Lax560851.WordArena

open Lax759944.BinaryWordEncoding

inductive Direction
  | minimize
  | maximize

structure Problem (Instance Solution : Type*) where
  direction : Direction
  feasible : Instance → Solution → Prop
  value : Instance → Solution → ℝ≥0
  input : Presentation Instance
  output : Solution → List ℕ
  input_faithful : input.Faithful
  output_injective : Function.Injective output

variable {Instance Solution : Type*}

def inputWords (problem : Problem Instance Solution) (x : Instance) : List ℕ :=
  (encode problem.input x).toInput

def inputSize (problem : Problem Instance Solution) (x : Instance) : ℕ :=
  bitSize (inputWords problem x)

end Lax213208.OptimizationProblem
end
