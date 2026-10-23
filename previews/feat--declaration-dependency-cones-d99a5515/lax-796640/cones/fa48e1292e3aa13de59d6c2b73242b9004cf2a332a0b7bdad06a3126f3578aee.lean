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

/-- Every requested identifier belongs to the supplied list. -/
def includes (available requested : List Nat) : Bool :=
  requested.all available.contains

/-- Set equality ignores order and repeated identifiers. -/
def sameMembers (left right : List Nat) : Bool :=
  includes left right && includes right left

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

/-- One round retains known declarations and adds their direct references. -/
def expand (s : Snapshot) (known : List Nat) : List Nat :=
  (known ++ known.flatMap (references s)).eraseDups

/-- Run a fixed number of rounds, using ordinary recursion on a natural number. -/
def expandFor (s : Snapshot) : Nat → List Nat → List Nat
  | 0, known => known
  | rounds + 1, known => expandFor s rounds (expand s known)

/-- The proposed executable collector, with its finite bound built in. -/
def reachable (s : Snapshot) (start : Nat) : List Nat :=
  expandFor s s.declarations.length [start]

/-- Test the recorded kind of a declaration. -/
def isAxiom (s : Snapshot) (id : Nat) : Bool :=
  (declaration s id).any (fun d => d.kind == .axiomDecl)

/-- The specification of an axiom dependency uses finite paths. -/
def UsesAxiom (s : Snapshot) (start axiomId : Nat) : Prop :=
  Reaches s start axiomId ∧ isAxiom s axiomId = true

/-- Compute dependencies from references, never from an author's claimed list. -/
def axiomsUsed (s : Snapshot) (start : Nat) : List Nat :=
  (reachable s start).filter (isAxiom s)

end Lax796640.Dependencies
end

-- Lax796640.Validation
section
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

/-- Statements used by a theorem, after removing permitted background axioms. -/
def assumptionsOf (s : Snapshot) (theoremId : Nat) : List Nat :=
  (axiomsUsed s theoremId).filter (fun a => !(backgroundAxiom s a))

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

/-- Check the declaration policy using computed axiom dependencies. -/
def checkDeclaration (s : Snapshot) (d : Declaration) : Bool :=
  match package s d.package with
  | none => false
  | some p =>
      match p.role with
      | .background => true
      | .concepts =>
          (d.kind != .axiomDecl || d.isProposition) &&
          (axiomsUsed s d.id).all (fun a => backgroundAxiom s a ||
            (d.kind == .axiomDecl && a == d.id))
      | .proofs =>
          (axiomsUsed s d.id).all (fun a => backgroundAxiom s a ||
            allowedStatement s d.package a)

/-- Check a proof claim; author-supplied assumptions can never hide a dependency. -/
def checkClaim (s : Snapshot) (c : Claim) : Bool :=
  (declaration s c.theoremId).any (fun d =>
    d.kind == .theoremDecl &&
    (package s d.package).any (fun p => p.role == .proofs) &&
    allowedStatement s d.package c.statementId && comparisonAgrees s c &&
    match c.claimedAssumptions with
    | none => true
    | some claimed => sameMembers claimed (assumptionsOf s c.theoremId))

/-- Proposed production entry point for mathematical validation.
This function is executable; it does not call any stated proof obligation. -/
def validate (s : Snapshot) : Bool :=
  checkTables s && s.declarations.all (checkDeclaration s) &&
  (s.claims.map Claim.theoremId).eraseDups.length == s.claims.length &&
  s.claims.all (checkClaim s)

/-- The network recorded after acceptance, built from recomputed assumptions. -/
def network (s : Snapshot) : Network where
  statements := (s.declarations.map Declaration.id).filter (isStatement s)
  rules := s.claims.map (fun c =>
    { proofId := c.theoremId, assumptions := assumptionsOf s c.theoremId,
      conclusion := c.statementId })

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

/-- Main mathematical guarantee for the computed closure of accepted records. -/
axiom established_sound (s : Snapshot) (meaning : Nat → Prop)
    (kernel : KernelContract s meaning) (accepted : validate s = true)
    (initial : List Nat) (admitted : ∀ a ∈ initial, a ∈ (network s).statements)
    (assumptions : ∀ a ∈ initial, meaning a) (a : Nat)
    (established : a ∈ closure (network s) initial) : meaning a

end Lax796640.RelativeSoundness
end
