-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax796640.Declarations
section
namespace Lax796640
end Lax796640

namespace Lax796640.Declarations
end Lax796640.Declarations

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
end Lax796640.Pipeline

namespace Lax796640.Pipeline.ArtifactKey
end Lax796640.Pipeline.ArtifactKey

namespace Lax796640.Pipeline.Event
end Lax796640.Pipeline.Event

namespace Lax796640.Pipeline.State
end Lax796640.Pipeline.State

namespace Lax796640.Pipeline.step
end Lax796640.Pipeline.step

namespace Lax796640.Pipeline.Event.conceptsReplayed
end Lax796640.Pipeline.Event.conceptsReplayed

namespace Lax796640.Pipeline.Event.failed
end Lax796640.Pipeline.Event.failed

namespace Lax796640.Pipeline.Event.inspected
end Lax796640.Pipeline.Event.inspected

namespace Lax796640.Pipeline.Event.proofsReplayed
end Lax796640.Pipeline.Event.proofsReplayed
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

-- Lax796640.RelativeSoundness
section
namespace Lax796640.RelativeSoundness
end Lax796640.RelativeSoundness

namespace Lax796640.RelativeSoundness.KernelContract
end Lax796640.RelativeSoundness.KernelContract
end

-- Lax796640.Production
section
namespace Lax796640.Production.validateAndClassify
end Lax796640.Production.validateAndClassify

namespace Lax796640.Production

open Declarations ProofNetworks Certificates Validation RelativeSoundness Pipeline

/-- A classification retains the assumptions on which it depends. -/
structure Classification where
  assumed : List Nat
  established : List Nat
  deriving DecidableEq, BEq, Repr

end Lax796640.Production
end
