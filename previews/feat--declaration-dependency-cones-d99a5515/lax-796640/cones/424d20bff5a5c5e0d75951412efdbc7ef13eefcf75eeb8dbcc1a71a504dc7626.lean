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

/-- The graph conditions needed for bounded dependency traversal. -/
def ReferencesWellFormed (s : Snapshot) : Prop :=
  (s.declarations.map Declaration.id).Nodup ∧
  ∀ d ∈ s.declarations, ∀ id ∈ d.references,
    ∃ target ∈ s.declarations, target.id = id

end Lax796640.Declarations
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

/-- An admissible statement is a propositional axiom of a concept package. -/
def isStatement (s : Snapshot) (id : Nat) : Bool :=
  (declaration s id).any (fun d =>
    d.kind == .axiomDecl && d.isProposition &&
    (package s d.package).any (fun p => p.role == .concepts))

/-- A proof package may assume statements only from directly required concepts. -/
def allowedStatement (s : Snapshot) (proofPackage statement : Nat) : Bool :=
  isStatement s statement &&
    (package s proofPackage).any (fun p =>
      (declaration s statement).any (fun d => p.requires.contains d.package))

/-- An explicit successful comparison for this particular theorem and conclusion. -/
def comparisonAgrees (s : Snapshot) (c : Claim) : Bool :=
  s.comparisons.any (fun f => f.theoremId == c.theoremId &&
    f.statementId == c.statementId && f.sameType && f.conclusionImported)

/-- Declarative requirements on identifiers, package relationships, and references. -/
def TablesValid (s : Snapshot) : Prop :=
  ReferencesWellFormed s ∧
  (s.declarations.map Declaration.name).Nodup ∧
  (s.packages.map Package.id).Nodup ∧ s.localPackages.Nodup ∧
  (∀ id ∈ s.localPackages, ∃ p ∈ s.packages, p.id = id) ∧
  (∀ d ∈ s.declarations, ∃ p ∈ s.packages, p.id = d.package) ∧
  (∀ p ∈ s.packages,
    p.environment = s.environment ∧
    (p.role = .background ∨ p.id ∈ s.localPackages ∨ p.registered = true) ∧
    (∀ id ∈ p.requires, ∃ q ∈ s.packages, q.id = id) ∧
    (p.role = .concepts → ∀ id ∈ p.requires,
      ∀ q ∈ s.packages, q.id = id → q.role ≠ .proofs)) ∧
  (∀ f ∈ s.comparisons,
    (∃ d ∈ s.declarations, d.id = f.theoremId) ∧
    (∃ d ∈ s.declarations, d.id = f.statementId))

/-- The axiom policy for one declaration, stated without the collector program. -/
def DeclarationValid (s : Snapshot) (d : Declaration) : Prop :=
  ∃ p ∈ s.packages, p.id = d.package ∧
    match p.role with
    | .background => True
    | .concepts =>
        (d.kind = .axiomDecl → d.isProposition = true) ∧
        ∀ a, UsesAxiom s d.id a →
          backgroundAxiom s a = true ∨ (d.kind = .axiomDecl ∧ a = d.id)
    | .proofs =>
        ∀ a, UsesAxiom s d.id a →
          backgroundAxiom s a = true ∨ allowedStatement s d.package a = true

/-- A proof claim agrees with declaration facts and with its actual dependencies. -/
def ClaimValid (s : Snapshot) (c : Claim) : Prop :=
  ∃ d ∈ s.declarations, d.id = c.theoremId ∧ d.kind = .theoremDecl ∧
    (package s d.package).any (fun p => p.role == .proofs) = true ∧
    allowedStatement s d.package c.statementId = true ∧
    comparisonAgrees s c = true ∧
    ∀ claimed, c.claimedAssumptions = some claimed →
      ∀ a, a ∈ claimed ↔ UsesAxiom s c.theoremId a ∧ backgroundAxiom s a = false

/-- The independent mathematical specification of acceptance. -/
def Valid (s : Snapshot) : Prop :=
  TablesValid s ∧ (∀ d ∈ s.declarations, DeclarationValid s d) ∧
  (s.claims.map Claim.theoremId).Nodup ∧ (∀ c ∈ s.claims, ClaimValid s c)

end Lax796640.Validation
end
