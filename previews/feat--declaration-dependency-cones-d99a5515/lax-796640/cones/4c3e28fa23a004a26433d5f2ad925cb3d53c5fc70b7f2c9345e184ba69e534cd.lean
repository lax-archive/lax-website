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

namespace Lax796640.ProofNetworks.closeFor
end Lax796640.ProofNetworks.closeFor

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

end Lax796640.ProofNetworks
end

-- Lax796640.Certificates
section
namespace Lax796640.Certificates

open Declarations ProofNetworks

/-- A step names the statement being established and the proof rule used. -/
structure Step where
  statement : Nat
  proofId : Nat
  deriving DecidableEq, BEq, Repr

/-- Check witnesses in order; each new statement must have a grounded proof. -/
def checkSteps (n : Network) : List Nat → List Step → Option (List Nat)
  | known, [] => some known.eraseDups
  | known, step :: rest =>
      if !known.contains step.statement && n.rules.any (fun r =>
          r.proofId == step.proofId && r.conclusion == step.statement &&
          includes known r.assumptions) then
        checkSteps n (known ++ [step.statement]) rest
      else none

/-- Check that every enabled proof rule has its conclusion in the result. -/
def checkClosed (n : Network) (known : List Nat) : Bool :=
  n.rules.all (fun r => !(includes known r.assumptions) || known.contains r.conclusion)

/-- Proposed production entry point for checking an entire classification. -/
def check (n : Network) (initial : List Nat) (steps : List Step) : Option (List Nat) :=
  match checkSteps n initial steps with
  | none => none
  | some known => if checkClosed n known then some known else none

end Lax796640.Certificates
end
