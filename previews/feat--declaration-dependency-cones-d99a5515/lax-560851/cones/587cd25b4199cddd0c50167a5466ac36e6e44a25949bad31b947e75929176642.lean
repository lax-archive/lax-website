-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Pairing

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

end Presentation

end Lax560851.StructuralPresentation
end

-- Lax560851.StructuralCombinators
section
namespace Lax560851.StructuralCombinators.Derivable
end Lax560851.StructuralCombinators.Derivable

namespace Lax560851.StructuralCombinators.Lawful
end Lax560851.StructuralCombinators.Lawful

namespace Lax560851.StructuralCombinators.SizeLaws
end Lax560851.StructuralCombinators.SizeLaws

namespace Lax560851.StructuralCombinators.Raw.constructorCharsCode
end Lax560851.StructuralCombinators.Raw.constructorCharsCode

namespace Lax560851.StructuralCombinators.Raw.fields
end Lax560851.StructuralCombinators.Raw.fields

namespace Lax560851.StructuralCombinators

open Lax560851.StructuralPresentation

open Lax560851.StructuralPresentation.Presentation

universe u v

namespace Raw

end Raw

/-- Structural presentation of natural numbers. -/
def nat : Presentation Nat where
  toRaw := .nat
  fromRaw
    | .nat n => some n
    | _ => none

/-- Structural presentation of a product. -/
def prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    Presentation (α × β) where
  toRaw x := .pair (A.toRaw x.1) (B.toRaw x.2)
  fromRaw
    | .pair a b =>
        match A.fromRaw a with
        | none => none
        | some x =>
            match B.fromRaw b with
            | none => none
            | some y => some (x, y)
    | _ => none

/-- Universal structural representation of a list. -/
def listToRaw {α : Type u} (P : Presentation α) : List α → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair (P.toRaw x) (listToRaw P xs)

/-- Partial inverse of `listToRaw`. -/
def listFromRaw {α : Type u} (P : Presentation α) : StructuralPresentation.Raw → Option (List α)
  | .nat 0 => some []
  | .pair x xs => do
      let x ← P.fromRaw x
      let xs ← listFromRaw P xs
      pure (x :: xs)
  | _ => none

/-- Cons-list structural presentation. -/
def list {α : Type u} (P : Presentation α) : Presentation (List α) where
  toRaw := listToRaw P
  fromRaw := listFromRaw P

/-- Evidence that a presentation was obtained solely from the fixed primitive
and combinator vocabulary. Unlike an unconstrained presentation typeclass,
this witness cannot certify an advice-bearing encoder. -/
inductive Generated : {α : Type} → Presentation α → Prop
  | nat : Generated StructuralCombinators.nat
  | prod {α β : Type} {A : Presentation α} {B : Presentation β} :
      Generated A → Generated B → Generated (StructuralCombinators.prod A B)
  | list {α : Type} {P : Presentation α} :
      Generated P → Generated (StructuralCombinators.list P)

end Lax560851.StructuralCombinators
end
