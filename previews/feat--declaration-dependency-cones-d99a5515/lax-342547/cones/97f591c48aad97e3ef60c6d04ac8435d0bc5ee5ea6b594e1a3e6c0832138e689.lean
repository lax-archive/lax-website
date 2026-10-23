-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.SetTheory.Cardinal.Finite

-- Lax342547.MomentSpace
section
namespace Lax342547.MomentSpace.baseEval
end Lax342547.MomentSpace.baseEval

namespace Lax342547.MomentSpace

abbrev Binary := ZMod 2

variable {Label Coord Base : Type}

end Lax342547.MomentSpace
end

-- Lax342547.ExactPins
section
namespace Lax342547.ExactPins

open Lax342547.MomentSpace

def Pin (Axis I N : Type) :=
  Σ S : Axis → Submodule Binary (I → Binary), ∀ a, S a →ₗ[Binary] (N → Binary)

namespace Pin

variable {Axis I N : Type}

def space (P : Pin Axis I N) (a : Axis) : Submodule Binary (I → Binary) := P.1 a

def value (P : Pin Axis I N) (a : Axis) : P.space a →ₗ[Binary] (N → Binary) := P.2 a

def Extends (P Q : Pin Axis I N) : Prop :=
  ∃ h : ∀ a, P.space a ≤ Q.space a,
    ∀ a (v : P.space a), Q.value a ⟨v.val, h a v.property⟩ = P.value a v

noncomputable def rank [Fintype Axis] (P : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary (P.space a)

def event {Ω : Type} (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) : Set Ω :=
  {o | ∀ a (v : P.space a), A o a v.val = P.value a v}

end Pin

end Lax342547.ExactPins
end

-- Lax342547.MetadataPins
section
namespace Lax342547.MetadataPins

open Lax342547.MomentSpace Lax342547.ExactPins

def Images {Axis I : Type} (N : Type) (S : Axis → Submodule Binary (I → Binary)) :=
  ∀ a, S a →ₗ[Binary] (N → Binary)

def Key {J Axis I : Type} (N : Type) (S : J → Axis → Submodule Binary (I → Binary)) :=
  Σ j, Images N (S j)

def record {Ω J Axis I N : Type}
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (choice : Ω → J)
    (S : J → Axis → Submodule Binary (I → Binary)) (o : Ω) : Key N S :=
  ⟨choice o, fun a => (A o a).comp (S (choice o) a).subtype⟩

def pin {J Axis I N : Type} {S : J → Axis → Submodule Binary (I → Binary)}
    (k : Key N S) : Pin Axis I N := ⟨S k.1, k.2⟩

axiom refined_fiber {Ω J Axis I N : Type} [Fintype Axis] [Fintype I]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (choice : Ω → J)
    (S : J → Axis → Submodule Binary (I → Binary)) (u : ℕ)
    (hu : ∀ j, ∑ a, Module.finrank Binary (S j a) ≤ u)
    (P₀ : Pin Axis I N) (R : Set Ω) (hR : R ⊆ P₀.event A) (o : Ω) (ho : o ∈ R) :
    ∃ P : Pin Axis I N, P₀.Extends P ∧ (pin (record A choice S o)).Extends P ∧
      P.rank ≤ P₀.rank + u ∧
      R ∩ {x | record A choice S x = record A choice S o} ⊆ P.event A

end Lax342547.MetadataPins
end
