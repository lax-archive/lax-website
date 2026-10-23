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
namespace Lax796640.Validation
end Lax796640.Validation

namespace Lax796640.Validation.DeclarationValid
end Lax796640.Validation.DeclarationValid

namespace Lax796640.Validation.checkClaim
end Lax796640.Validation.checkClaim

namespace Lax796640.Validation.checkDeclaration
end Lax796640.Validation.checkDeclaration
end

-- Lax796640.Pipeline
section
namespace Lax796640.Pipeline

open Declarations Validation

/-- The identity shared by replay, inspection, and the eventual publication. -/
structure ArtifactKey where
  sourceCommit : String
  environment : String
  captureDigest : String
  dependencyDigest : String
  deriving DecidableEq, BEq, Repr

/-- Reports from the external runner. Authenticating them is outside this controller. -/
inductive Event where
  | conceptsReplayed (key : ArtifactKey)
  | proofsReplayed (key : ArtifactKey)
  | inspected (key : ArtifactKey) (data : Snapshot)
  | failed
  deriving DecidableEq, BEq, Repr

/-- Accumulated evidence for one artifact. -/
structure State where
  key : ArtifactKey
  conceptsReplayed : Bool
  proofsReplayed : Bool
  inspection : Option Snapshot
  failed : Bool
  deriving DecidableEq, BEq, Repr

/-- Starting a run clears every receipt, even if another run just succeeded. -/
def start (key : ArtifactKey) : State :=
  { key, conceptsReplayed := false, proofsReplayed := false,
    inspection := none, failed := false }

/-- Advance the controller. A failure is permanent within this run. -/
def step (state : State) (event : Event) : State :=
  if state.failed then state else
  match event with
  | .failed => { state with failed := true }
  | .conceptsReplayed key =>
      if key == state.key then { state with conceptsReplayed := true } else state
  | .proofsReplayed key =>
      if key == state.key then { state with proofsReplayed := true } else state
  | .inspected key data =>
      if key == state.key then { state with inspection := some data } else state

/-- Execute a finite sequence of runner events. -/
def run (key : ArtifactKey) (events : List Event) : State :=
  events.foldl step (start key)

end Lax796640.Pipeline
end
