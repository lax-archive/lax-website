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

/-- Find a package by its identifier. -/
def package (s : Snapshot) (id : Nat) : Option Package :=
  s.packages.find? (fun p => p.id == id)

/-- Every requested identifier belongs to the supplied list. -/
def includes (available requested : List Nat) : Bool :=
  requested.all available.contains

end Lax796640.Declarations
end

-- Lax796640.Dependencies
section
namespace Lax796640.Dependencies
end Lax796640.Dependencies

namespace Lax796640.Dependencies.Reaches
end Lax796640.Dependencies.Reaches

namespace Lax796640.Dependencies.expandFor
end Lax796640.Dependencies.expandFor
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

/-- Check finite table integrity before relying on lookups. -/
def checkTables (s : Snapshot) : Bool :=
  let declIds := s.declarations.map Declaration.id
  let declNames := s.declarations.map Declaration.name
  let packageIds := s.packages.map Package.id
  declIds.eraseDups.length == declIds.length &&
  declNames.eraseDups.length == declNames.length &&
  packageIds.eraseDups.length == packageIds.length &&
  s.localPackages.eraseDups.length == s.localPackages.length &&
  includes packageIds s.localPackages &&
  s.declarations.all (fun d => packageIds.contains d.package &&
    includes declIds d.references) &&
  s.packages.all (fun p => p.environment == s.environment &&
    (p.role == .background || s.localPackages.contains p.id || p.registered) &&
    includes packageIds p.requires &&
    (p.role != .concepts || p.requires.all (fun id =>
      (package s id).any (fun q => q.role != .proofs)))) &&
  s.comparisons.all (fun f => declIds.contains f.theoremId &&
    declIds.contains f.statementId)

end Lax796640.Validation
end
