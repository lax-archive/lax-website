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

-- Lax796640.ProofNetworks
section
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

/-- Establish a statement from designated assumptions using finitely many rules. -/
inductive Derivable (n : Network) (initial : List Nat) : Nat → Prop where
  | assumption {statement : Nat} :
      statement ∈ initial → Derivable n initial statement
  | apply {r : Rule} : r ∈ n.rules →
      (∀ a ∈ r.assumptions, Derivable n initial a) →
      Derivable n initial r.conclusion

end Lax796640.ProofNetworks
end

-- Lax796640.Stability
section
namespace Lax796640.Stability

open ProofNetworks

/-- Derivations of the assumptions can be substituted into a derivation. -/
axiom discharge_assumptions (n : Network) (initial replacement : List Nat)
    (discharge : ∀ a ∈ initial, Derivable n replacement a) (a : Nat) :
    Derivable n initial a → Derivable n replacement a

end Lax796640.Stability
end
