-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.List.Basic

-- Lax796640.Declarations
section
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

/-- An author's request to record a theorem as a proof of a statement. -/
structure Claim where
  theoremId : Nat
  statementId : Nat
  /-- Optional documentation, cross-checked against computed dependencies. -/
  claimedAssumptions : Option (List Nat)
  deriving DecidableEq, BEq, Repr

end Lax796640.Declarations
end
