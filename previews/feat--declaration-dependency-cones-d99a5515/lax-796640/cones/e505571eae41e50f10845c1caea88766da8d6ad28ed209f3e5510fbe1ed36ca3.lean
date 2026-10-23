-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax796640.Declarations
section
namespace Lax796640.Declarations.Claim
end Lax796640.Declarations.Claim

namespace Lax796640.Declarations.Comparison
end Lax796640.Declarations.Comparison

namespace Lax796640.Declarations.Declaration
end Lax796640.Declarations.Declaration

namespace Lax796640.Declarations.DeclarationKind
end Lax796640.Declarations.DeclarationKind

namespace Lax796640.Declarations.Package
end Lax796640.Declarations.Package

namespace Lax796640.Declarations.PackageRole
end Lax796640.Declarations.PackageRole

namespace Lax796640.Declarations.Snapshot
end Lax796640.Declarations.Snapshot

namespace Lax796640.Declarations.DeclarationKind.axiomDecl
end Lax796640.Declarations.DeclarationKind.axiomDecl

namespace Lax796640.Declarations.DeclarationKind.other
end Lax796640.Declarations.DeclarationKind.other

namespace Lax796640.Declarations.DeclarationKind.theoremDecl
end Lax796640.Declarations.DeclarationKind.theoremDecl

namespace Lax796640.Declarations.PackageRole.background
end Lax796640.Declarations.PackageRole.background

namespace Lax796640.Declarations.PackageRole.concepts
end Lax796640.Declarations.PackageRole.concepts

namespace Lax796640.Declarations.PackageRole.proofs
end Lax796640.Declarations.PackageRole.proofs

namespace Lax796640.Declarations

/-- Every requested identifier belongs to the supplied list. -/
def includes (available requested : List Nat) : Bool :=
  requested.all available.contains

end Lax796640.Declarations
end

-- Lax796640.ProofNetworks
section
namespace Lax796640.ProofNetworks.Derivable
end Lax796640.ProofNetworks.Derivable

namespace Lax796640.ProofNetworks

open Declarations

/-- One conditional proof, identified by its theorem declaration. -/
structure Rule where
  proofId : Nat
  assumptions : List Nat
  conclusion : Nat
  deriving DecidableEq, BEq, Repr

/-- Statements and the available rules for establishing them. -/
structure Network where
  statements : List Nat
  rules : List Rule
  deriving DecidableEq, BEq, Repr

/-- Rules refer to existing statements and have distinct proof identifiers. -/
def WellFormed (n : Network) : Prop :=
  n.statements.Nodup ∧ (n.rules.map Rule.proofId).Nodup ∧
  ∀ r ∈ n.rules, r.conclusion ∈ n.statements ∧
    ∀ a ∈ r.assumptions, a ∈ n.statements

/-- One round of the executable closure algorithm. -/
def advance (n : Network) (known : List Nat) : List Nat :=
  (known ++ (n.rules.filter (fun r => includes known r.assumptions)).map
    Rule.conclusion).eraseDups

/-- Each recursive call consumes one round. -/
def closeFor (n : Network) : Nat → List Nat → List Nat
  | 0, known => known.eraseDups
  | rounds + 1, known => closeFor n rounds (advance n known)

/-- At most one round per statement suffices, even in a cyclic network. -/
def closure (n : Network) (initial : List Nat) : List Nat :=
  closeFor n n.statements.length initial

end Lax796640.ProofNetworks
end

-- Lax796640.Stability
section
namespace Lax796640.Stability

open ProofNetworks

/-- Recomputing closure from an already closed result changes no membership. -/
axiom closure_idempotent (n : Network) (h : WellFormed n) (initial : List Nat)
    (admitted : ∀ a ∈ initial, a ∈ n.statements) (a : Nat) :
    a ∈ closure n (closure n initial) ↔ a ∈ closure n initial

end Lax796640.Stability
end
