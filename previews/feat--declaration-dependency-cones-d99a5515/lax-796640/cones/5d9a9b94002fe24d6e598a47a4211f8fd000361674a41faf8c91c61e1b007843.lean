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

/-- Approval requires both replays, an inspection in this environment,
and acceptance by the concrete mathematical validator. -/
def approve (state : State) : Bool :=
  !state.failed && state.conceptsReplayed && state.proofsReplayed &&
    state.inspection.any (fun data =>
      data.environment == state.key.environment && validate data)

/-- The exact inspected input approved at the end of this run, if any. -/
def approvedInput (key : ArtifactKey) (events : List Event) : Option Snapshot :=
  let state := run key events
  if approve state then state.inspection else none

end Lax796640.Pipeline
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

-- Lax796640.RelativeSoundness
section
namespace Lax796640.RelativeSoundness
end Lax796640.RelativeSoundness

namespace Lax796640.RelativeSoundness.KernelContract
end Lax796640.RelativeSoundness.KernelContract
end

-- Lax796640.Production
section
namespace Lax796640.Production

open Declarations ProofNetworks Certificates Validation RelativeSoundness Pipeline

/-- A classification retains the assumptions on which it depends. -/
structure Classification where
  assumed : List Nat
  established : List Nat
  deriving DecidableEq, BEq, Repr

/-- Proposed production entry point for classification relative to assumptions. -/
def validateAndClassify (key : ArtifactKey) (events : List Event)
    (initial : List Nat) (certificate : List Step) : Option Classification :=
  match approvedInput key events with
  | none => none
  | some data =>
      let n := network data
      if includes n.statements initial then
        (check n initial certificate).map (fun known =>
          { assumed := initial.eraseDups, established := known })
      else none

/-- A failure in the runner cannot yield a successful final classification. -/
axiom production_rejects_failure (key : ArtifactKey) (events : List Event)
    (failed : Event.failed ∈ events) (initial : List Nat) (certificate : List Step) :
    validateAndClassify key events initial certificate = none

end Lax796640.Production
end
