-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax796640.Declarations
section
namespace Lax796640.Declarations

/-- Background packages are the pinned Lean and Mathlib environment. -/
inductive PackageRole where
  | background
  | concepts
  | proofs
  deriving DecidableEq, BEq, Repr

/-- Only the distinctions needed for the mathematical validation rules. -/
inductive DeclarationKind where
  | axiomDecl
  | theoremDecl
  | other
  deriving DecidableEq, BEq, Repr

/-- A package and the packages it directly requires. -/
structure Package where
  id : Nat
  role : PackageRole
  environment : String
  registered : Bool
  requires : List Nat
  deriving DecidableEq, BEq, Repr

/-- Facts extracted from one kernel-checked declaration. -/
structure Declaration where
  id : Nat
  name : String
  package : Nat
  kind : DeclarationKind
  /-- Whether the declared type itself has type `Prop`. -/
  isProposition : Bool
  /-- References from types, bodies, and structural links to constructors. -/
  references : List Nat
  deriving DecidableEq, BEq, Repr

/-- A kernel comparison and an import check for a proposed conclusion. -/
structure Comparison where
  theoremId : Nat
  statementId : Nat
  sameType : Bool
  conclusionImported : Bool
  deriving DecidableEq, BEq, Repr

/-- An author's request to record a theorem as a proof of a statement. -/
structure Claim where
  theoremId : Nat
  statementId : Nat
  /-- Optional documentation, cross-checked against computed dependencies. -/
  claimedAssumptions : Option (List Nat)
  deriving DecidableEq, BEq, Repr

/-- One environment and its complete relevant declaration table.
`localPackages` are being validated now; other non-background packages must
already be registered. Imported packages still have their declarations here.
-/
structure Snapshot where
  environment : String
  localPackages : List Nat
  packages : List Package
  declarations : List Declaration
  comparisons : List Comparison
  claims : List Claim
  deriving DecidableEq, BEq, Repr

/-- Find a declaration. Duplicate identifiers are rejected before acceptance. -/
def declaration (s : Snapshot) (id : Nat) : Option Declaration :=
  s.declarations.find? (fun d => d.id == id)

/-- Find a package by its identifier. -/
def package (s : Snapshot) (id : Nat) : Option Package :=
  s.packages.find? (fun p => p.id == id)

end Lax796640.Declarations
end

-- Lax796640.ProofNetworks
section
namespace Lax796640.ProofNetworks
end Lax796640.ProofNetworks

namespace Lax796640.ProofNetworks.Derivable
end Lax796640.ProofNetworks.Derivable

namespace Lax796640.ProofNetworks.Network
end Lax796640.ProofNetworks.Network

namespace Lax796640.ProofNetworks.Rule
end Lax796640.ProofNetworks.Rule

namespace Lax796640.ProofNetworks.closeFor
end Lax796640.ProofNetworks.closeFor
end

-- Lax796640.Certificates
section
namespace Lax796640.Certificates
end Lax796640.Certificates

namespace Lax796640.Certificates.Step
end Lax796640.Certificates.Step

namespace Lax796640.Certificates.check
end Lax796640.Certificates.check

namespace Lax796640.Certificates.checkSteps
end Lax796640.Certificates.checkSteps
end

-- Lax796640.Dependencies
section
namespace Lax796640.Dependencies.expandFor
end Lax796640.Dependencies.expandFor

namespace Lax796640.Dependencies

open Declarations

/-- The direct references of a declaration; absent entries have no references.
Missing referenced declarations are nevertheless rejected by validation. -/
def references (s : Snapshot) (id : Nat) : List Nat :=
  ((declaration s id).map Declaration.references).getD []

/-- A finite path in the graph of constant references. -/
inductive Reaches (s : Snapshot) : Nat → Nat → Prop where
  | self (id : Nat) : Reaches s id id
  | next {start middle finish : Nat} :
      Reaches s start middle → finish ∈ references s middle →
      Reaches s start finish

/-- Test the recorded kind of a declaration. -/
def isAxiom (s : Snapshot) (id : Nat) : Bool :=
  (declaration s id).any (fun d => d.kind == .axiomDecl)

/-- The specification of an axiom dependency uses finite paths. -/
def UsesAxiom (s : Snapshot) (start axiomId : Nat) : Prop :=
  Reaches s start axiomId ∧ isAxiom s axiomId = true

end Lax796640.Dependencies
end

-- Lax796640.Validation
section
namespace Lax796640.Validation.DeclarationValid
end Lax796640.Validation.DeclarationValid

namespace Lax796640.Validation.checkClaim
end Lax796640.Validation.checkClaim

namespace Lax796640.Validation.checkDeclaration
end Lax796640.Validation.checkDeclaration

namespace Lax796640.Validation

open Declarations Dependencies ProofNetworks

/-- The fixed background axiom policy of the intended Lax environment. -/
def backgroundNames : List String :=
  ["propext", "Classical.choice", "Quot.sound"]

/-- A background axiom must have both the right name and a background origin. -/
def backgroundAxiom (s : Snapshot) (id : Nat) : Bool :=
  (declaration s id).any (fun d =>
    d.kind == .axiomDecl && backgroundNames.contains d.name &&
    (package s d.package).any (fun p => p.role == .background))

end Lax796640.Validation
end

-- Lax796640.RelativeSoundness
section
namespace Lax796640.RelativeSoundness

open Declarations Dependencies ProofNetworks Validation Certificates

/-- The explicit logical interface to replay and faithful inspection.
`meaning id` denotes the proposition expressed by the declaration's type;
the contract is used only for theorems and their axiom dependencies.
-/
structure KernelContract (s : Snapshot) (meaning : Nat → Prop) : Prop where
  /-- Kernel-checked theorem bodies establish their types from their axiom leaves. -/
  theoremSound : ∀ d ∈ s.declarations, d.kind = .theoremDecl →
    (∀ a, UsesAxiom s d.id a → meaning a) → meaning d.id
  /-- Conversion compares the actual types, rather than their printed text. -/
  comparisonSound : ∀ f ∈ s.comparisons, f.sameType = true →
    (meaning f.theoremId ↔ meaning f.statementId)
  /-- The three permitted background axioms hold in the chosen interpretation. -/
  backgroundSound : ∀ a, backgroundAxiom s a = true → meaning a

end Lax796640.RelativeSoundness
end
