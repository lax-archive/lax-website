-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Computability.Partrec
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Basic
import Mathlib.ModelTheory.Semantics

-- Lax52.MSOSyntax
noncomputable section
namespace Lax52.MSOSyntax

open FirstOrder

universe u v

/-- Monadic second-order formulas over `L`, intrinsically scoped by the numbers
of available first-order and monadic variables. -/
inductive Formula (L : Language.{u, v}) : Nat → Nat → Type (max u v)
  | falsum {n m : Nat} : Formula L n m
  | equal {n m : Nat} : L.Term (Fin n) → L.Term (Fin n) → Formula L n m
  | rel {n m k : Nat} : L.Relations k → (Fin k → L.Term (Fin n)) → Formula L n m
  | mem {n m : Nat} : L.Term (Fin n) → Fin m → Formula L n m
  | or {n m : Nat} : Formula L n m → Formula L n m → Formula L n m
  | neg {n m : Nat} : Formula L n m → Formula L n m
  | exFO {n m : Nat} : Formula L (n + 1) m → Formula L n m
  | exSO {n m : Nat} : Formula L n (m + 1) → Formula L n m

/-- An MSO sentence has no free variables of either sort. -/
abbrev Sentence (L : Language.{u, v}) := Formula L 0 0

namespace Formula

variable {L : Language.{u, v}} {n m : Nat}

end Formula

end Lax52.MSOSyntax
end

-- Lax53.RankedTree
noncomputable section
namespace Lax53.RankedTree.Node.child
end Lax53.RankedTree.Node.child

namespace Lax53.RankedTree.Node.inChild
end Lax53.RankedTree.Node.inChild

namespace Lax53.RankedTree.Node.label
end Lax53.RankedTree.Node.label

namespace Lax53.RankedTree.Node.root
end Lax53.RankedTree.Node.root

namespace Lax53.RankedTree.Node.rootOf
end Lax53.RankedTree.Node.rootOf

namespace Lax53.RankedTree

universe u

/-- A finite alphabet whose symbols have prescribed arities. -/
structure RankedAlphabet where
  Symbol : Type u
  [symbolsFintype : Fintype Symbol]
  [symbolsDecidableEq : DecidableEq Symbol]
  rank : Symbol → Nat

attribute [instance] RankedAlphabet.symbolsFintype

attribute [instance] RankedAlphabet.symbolsDecidableEq

/-- Finite terms over a ranked alphabet. A node labelled by `a` has one
ordered child for each element of `Fin (A.rank a)`. -/
inductive Tree (A : RankedAlphabet.{u}) : Type u
  | node (a : A.Symbol) (children : Fin (A.rank a) → Tree A) : Tree A

/-- The set of child slots occurring in the alphabet. Its zero-based index
`i` represents the slot customarily numbered `i+1`. -/
def ChildIndex (A : RankedAlphabet.{u}) : Type :=
  {i : Nat // ∃ a : A.Symbol, i < A.rank a}

namespace ChildIndex

end ChildIndex

namespace Node

end Node

end Lax53.RankedTree
end

-- Lax53.TreeAutomaton
noncomputable section
namespace Lax53.TreeAutomaton
end Lax53.TreeAutomaton

namespace Lax53.TreeAutomaton.Automaton
end Lax53.TreeAutomaton.Automaton

namespace Lax53.TreeAutomaton.Automaton.RunsTo
end Lax53.TreeAutomaton.Automaton.RunsTo
end

-- Lax52.MSOSemantics
noncomputable section
namespace Lax52.MSOSemantics
end Lax52.MSOSemantics

namespace Lax52.MSOSemantics.Realize
end Lax52.MSOSemantics.Realize
end

-- Lax53.TreeStructure
noncomputable section
namespace Lax53.TreeStructure.treeStructure
end Lax53.TreeStructure.treeStructure

namespace Lax53.TreeStructure

open FirstOrder

open FirstOrder.Language

open Lax53.RankedTree

universe u

/-- Relation symbols for ranked trees. -/
inductive TreeRelation (A : RankedAlphabet.{u}) : Nat → Type u
  | label (a : A.Symbol) : TreeRelation A 1
  | child (i : ChildIndex A) : TreeRelation A 2

/-- The first-order language of ranked trees over `A`. -/
def treeSignature (A : RankedAlphabet.{u}) : FirstOrder.Language.{0, u} where
  Functions := fun _ => Empty
  Relations := TreeRelation A

end Lax53.TreeStructure
end

-- Lax53.ValueTranslations
noncomputable section
namespace Lax53.ValueTranslations

open Lax52.MSOSyntax

open Lax53.RankedTree

open Lax53.TreeStructure

open Lax53.TreeAutomaton

/-- A finite ranked alphabet is described by listing the ranks of its symbols.
The symbol in position `i` has rank `code[i]`. -/
abbrev RankedAlphabetCode := List Nat

namespace RankedAlphabetCode

/-- The canonical ranked alphabet represented by a rank string. -/
def toRankedAlphabet (code : RankedAlphabetCode) : RankedAlphabet where
  Symbol := Fin code.length
  symbolsFintype := inferInstance
  symbolsDecidableEq := inferInstance
  rank i := code.get i

end RankedAlphabetCode

namespace AutomatonCode

end AutomatonCode

end Lax53.ValueTranslations
end

-- Lax58.StructuralPresentation
noncomputable section
namespace Lax58.StructuralPresentation

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

/-- Number of nodes in a universal structural representation. -/
def nodes : Raw → Nat
  | .nat _ => 1
  | .pair a b => nodes a + nodes b + 1

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

namespace Presentation

/-- Structural size before any serialization or memory layout is chosen. -/
def structuralSize {α : Type u} (P : Presentation α) (x : α) : Nat :=
  (P.toRaw x).nodes

end Presentation

end Lax58.StructuralPresentation
end

-- Lax58.StructuralCombinators
noncomputable section
namespace Lax58.StructuralCombinators.Lawful
end Lax58.StructuralCombinators.Lawful

namespace Lax58.StructuralCombinators.SizeLaws
end Lax58.StructuralCombinators.SizeLaws

namespace Lax58.StructuralCombinators

open Lax58.StructuralPresentation

open Lax58.StructuralPresentation.Presentation

universe u v

namespace Raw

/-- An injective numerical realization of character lists, used only inside
the named-constructor combinator. -/
def constructorCharsCode : List Char → Nat
  | [] => 0
  | c :: cs => Nat.pair c.toNat (constructorCharsCode cs) + 1

/-- The internal numerical realization of a symbolic constructor name. -/
def constructorNameCode (name : String) : Nat :=
  constructorCharsCode name.toList

/-- Structural representation of an ordered list of already represented fields. -/
def fields : List StructuralPresentation.Raw → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair x (fields xs)

/-- A symbolically named constructor occurrence with ordered fields. -/
def constructor (name : String) (xs : List StructuralPresentation.Raw) :
    StructuralPresentation.Raw :=
  .pair (.nat (constructorNameCode name)) (fields xs)

end Raw

/-- Structural presentation of natural numbers. -/
def nat : Presentation Nat where
  toRaw := .nat
  fromRaw
    | .nat n => some n
    | _ => none

/-- Structural presentation of a product. -/
def prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    Presentation (α × β) where
  toRaw x := .pair (A.toRaw x.1) (B.toRaw x.2)
  fromRaw
    | .pair a b =>
        match A.fromRaw a with
        | none => none
        | some x =>
            match B.fromRaw b with
            | none => none
            | some y => some (x, y)
    | _ => none

/-- Universal structural representation of a list. -/
def listToRaw {α : Type u} (P : Presentation α) : List α → StructuralPresentation.Raw
  | [] => .nat 0
  | x :: xs => .pair (P.toRaw x) (listToRaw P xs)

/-- Partial inverse of `listToRaw`. -/
def listFromRaw {α : Type u} (P : Presentation α) : StructuralPresentation.Raw → Option (List α)
  | .nat 0 => some []
  | .pair x xs => do
      let x ← P.fromRaw x
      let xs ← listFromRaw P xs
      pure (x :: xs)
  | _ => none

/-- Cons-list structural presentation. -/
def list {α : Type u} (P : Presentation α) : Presentation (List α) where
  toRaw := listToRaw P
  fromRaw := listFromRaw P

/-- Evidence that a presentation was obtained solely from the fixed primitive
and combinator vocabulary. Unlike an unconstrained presentation typeclass,
this witness cannot certify an advice-bearing encoder. -/
inductive Generated : {α : Type} → Presentation α → Prop
  | nat : Generated StructuralCombinators.nat
  | prod {α β : Type} {A : Presentation α} {B : Presentation β} :
      Generated A → Generated B → Generated (StructuralCombinators.prod A B)
  | list {α : Type} {P : Presentation α} :
      Generated P → Generated (StructuralCombinators.list P)

/-- A type whose presentation can be synthesized from the fixed structural
vocabulary. The accompanying derivation, rather than mere typeclass
membership, is the no-advice certificate. -/
class Derivable (α : Type) where
  presentation : Presentation α
  generated : Generated presentation

instance : Derivable Nat where
  presentation := nat
  generated := .nat

instance {α : Type} [P : Derivable α] : Derivable (List α) where
  presentation := list P.presentation
  generated := .list P.generated

/-- Presentation synthesized by recursively following the `Nat`, product,
and list structure of its type. -/
def derivedPresentation {α : Type} [P : Derivable α] : Presentation α :=
  P.presentation

end Lax58.StructuralCombinators
end

-- Lax58.CertifiedDerivation
noncomputable section
namespace Lax58.CertifiedDerivation

open Lax58.StructuralPresentation Lax58.StructuralCombinators

universe u

/-- A checked implementation of a specified canonical encoder and law.
Both specifications are type indices, so even tactics accessing the private
constructor cannot replace them. Provenance of the specifications comes from
the closed derivation command, which never accepts arbitrary witness values. -/
structure CertifiedFieldEncoding (α : Type u) (canonical : α → Raw) (laws : Prop) where
  private mk ::
  toRaw : α → Raw
  agrees : toRaw = canonical
  checked : laws

namespace CertifiedFieldEncoding

/-- Package a specified encoder with a proof of its law. This constructs only
an agreement value: it does not register a datatype or certify the provenance
of the supplied specification. The derivation command alone manages that
registry, after inspecting the source constructors. -/
def ofLaws {α : Type u} (canonical : α → Raw) {laws : Prop} (checked : laws) :
    CertifiedFieldEncoding α canonical laws :=
  ⟨canonical, rfl, checked⟩

/-- The natural-number primitive. -/
def nat : CertifiedFieldEncoding Nat Raw.nat (∀ n : Nat, Raw.nat n = Raw.nat n) :=
  ⟨Raw.nat, rfl, fun _ => rfl⟩

/-- Finite indices retain their natural value. -/
def fin (n : Nat) : CertifiedFieldEncoding (Fin n) (fun i => Raw.nat i.val)
    (∀ i : Fin n, Raw.nat i.val = Raw.nat i.val) :=
  ⟨fun i => Raw.nat i.val, rfl, fun _ => rfl⟩

/-- Erase only a subtype's proof, retaining its certified computational field. -/
def subtype {α : Type u} {canonical : α → Raw} {laws : Prop}
    (P : CertifiedFieldEncoding α canonical laws) (p : α → Prop) :
    CertifiedFieldEncoding (Subtype p) (fun x => canonical x.val) laws :=
  ⟨fun x => canonical x.val, rfl, P.checked⟩

/-- Enumerate a possibly dependent finite family in intrinsic index order. -/
def family {n : Nat} {α : Fin n → Type u}
    {canonical : (i : Fin n) → α i → Raw} {laws : Fin n → Prop}
    (P : (i : Fin n) → CertifiedFieldEncoding (α i) (canonical i) (laws i)) :
    CertifiedFieldEncoding ((i : Fin n) → α i)
      (fun f => Raw.fields (List.ofFn fun i => canonical i (f i))) (∀ i, laws i) :=
  ⟨fun f => Raw.fields (List.ofFn fun i => canonical i (f i)),
    rfl, fun i => (P i).checked⟩

end CertifiedFieldEncoding

end Lax58.CertifiedDerivation
end

-- Lax58.CertifiedDerivationElab
noncomputable section
namespace Lax58.CertifiedDerivationElab

open Lax58.StructuralPresentation Lax58.StructuralCombinators

open Lax58.CertifiedDerivation

open Lean Meta Elab Term Command

open Lean.Parser.Term

private initialize certifiedEncoders : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[] }

/-- Resolve only fixed primitives or a witness generated by this module's
command. In particular, neither `FieldEncoding` nor user instances are read. -/
private partial def certifiedField (type : Expr) : TermElabM Expr := do
  let type ← whnf type
  if type.isConstOf ``Nat then
    return mkConst ``CertifiedFieldEncoding.nat
  if type.isAppOfArity ``Fin 1 then
    return ← mkAppM ``CertifiedFieldEncoding.fin #[type.appArg!]
  if type.isAppOfArity ``Subtype 2 then
    let args := type.getAppArgs
    let base ← certifiedField args[0]!
    return ← mkAppM ``CertifiedFieldEncoding.subtype #[base, args[1]!]
  if let .forallE name domain body bi := type then
    let domain ← whnf domain
    if domain.isAppOfArity ``Fin 1 then
      return ← withLocalDecl name bi domain fun i => do
        let item ← certifiedField (body.instantiate1 i)
        mkAppM ``CertifiedFieldEncoding.family #[← mkLambdaFVars #[i] item]
  for name in certifiedEncoders.getState (← getEnv) do
    let saved ← saveState
    let candidate ← mkConstWithFreshMVarLevels name
    let (args, _, result) ← forallMetaTelescopeReducing (← inferType candidate)
    if result.isAppOfArity ``CertifiedFieldEncoding 3 &&
        (← isDefEq result.getAppArgs[0]! type) then
      let candidate ← instantiateMVars (mkAppN candidate args)
      if !candidate.hasExprMVar then
        return candidate
    saved.restore
  throwError "unsupported certified field type {type}; expected Nat, Fin, a proof-erased subtype, a finite family, or an earlier constructor-certified datatype"

private def recursiveType (indName : Name) (type : Expr) : TermElabM Bool := do
  return (← whnf type).getAppFn.constName? == some indName

private def explicitBinders : Expr → Expr
  | .lam name type body _ => .lam name type (explicitBinders body) .default
  | body => body

private def certifiedAlternative (indInfo : InductiveVal) (levels : List Level)
    (params : Array Expr)
    (recursiveCall : TSyntax `term) (constructorName : Name) :
    TermElabM (TSyntax ``matchAlt) := do
  let constructor ← getConstInfoCtor constructorName
  let ctorType ← inferType (mkAppN (mkConst constructorName levels) params)
  forallTelescopeReducing ctorType fun arguments result => do
    let mut lctx ← getLCtx
    for argument in arguments do
      let decl ← argument.fvarId!.getDecl
      lctx := lctx.setUserName argument.fvarId! (← mkFreshUserName decl.userName)
    withLCtx lctx (← getLocalInstances) do
      let mut patterns : Array (TSyntax `term) := #[]
      for _ in params do patterns := patterns.push (← `(_))
      let mut fields : Array (Ident × Expr × BinderInfo) := #[]
      for argument in arguments do
        let decl ← argument.fvarId!.getDecl
        let name := mkIdent decl.userName
        patterns := patterns.push name
        fields := fields.push (name, decl.type, decl.binderInfo)
      -- An actually empty field eliminates its whole constructor. This handles
      -- function-free first-order languages without accepting a user IsEmpty.
      for (name, type, _) in fields do
        let type ← whnf type
        if let .const emptyName _ := type.getAppFn then
          if let .inductInfo emptyInfo ← getConstInfo emptyName then
            if emptyInfo.ctors.isEmpty then
              return ← `(matchAltExpr|
                | @$(mkIdent constructor.name):ident $patterns:term* => nomatch $name:ident)
      let mut encoded : TSyntax `term ← `([])
      for (name, type, bi) in fields.reverse do
        if ← isProp type then continue
        -- Implicit fields must still pass validation. Only intrinsic indices
        -- (Nat/Fin in the present supported syntax) are erased.
        if !bi.isExplicit then
          let normalized ← whnf type
          unless normalized.isConstOf ``Nat || normalized.isAppOfArity ``Fin 1 do
            throwError "{constructorName}: unsupported implicit field {name}: {type}"
          let some decl := lctx.findFromUserName? name.getId
            | throwError "missing constructor field {name}"
          unless result.containsFVar decl.fvarId ||
              fields.any (fun (_, ty, _) => ty.containsFVar decl.fvarId) do
            throwError "{constructorName}: implicit field {name} is not an intrinsic index"
          continue
        if ← recursiveType indInfo.name type then
          encoded ← `(($recursiveCall) $name:ident :: $encoded)
        else
          let type ← whnf type
          if let .forallE _ domain body _ := type then
            if (← whnf domain).isAppOfArity ``Fin 1 &&
                (← recursiveType indInfo.name body) then
              encoded ← `(List.ofFn (fun i => ($recursiveCall) ($name:ident i)) ++ $encoded)
              continue
          let witness ← try certifiedField type catch ex =>
            throwError "{constructorName}, field {name}: {ex.toMessageData}"
          -- Embed the checked expression itself, abstracting constructor locals
          -- before leaving their telescope. Pretty-printer round trips would
          -- let downstream delaborators change the selected witness.
          let witnessFunction ← exprToSyntax (explicitBinders (← mkLambdaFVars arguments witness))
          let fieldNames : Array (TSyntax `term) := fields.map fun (id, _, _) => ⟨id.raw⟩
          encoded ← `((CertifiedFieldEncoding.toRaw
            ($witnessFunction $fieldNames*) $name:ident) :: $encoded)
      let tag := constructor.name.eraseMacroScopes.getString!
      `(matchAltExpr| | @$(mkIdent constructor.name):ident $patterns:term* =>
          Raw.constructor $(quote tag) $encoded)

private def alternativesFor (type : Expr) (recursiveCall : TSyntax `term) :
    TermElabM (Array (TSyntax ``matchAlt)) := do
  let type ← whnf type
  let some name := type.getAppFn.constName?
    | throwError "certified derivation expects an inductive datatype, got {type}"
  let info ← getConstInfoInduct name
  unless info.all.length == 1 do
    throwError "certified derivation does not support mutual inductives: {name}"
  let params := type.getAppArgs.extract 0 info.numParams
  return (← info.ctors.mapM
    (certifiedAlternative info type.getAppFn.constLevels! params recursiveCall)).toArray

elab "certifiedFun% " "using " recursiveCall:term : term <= expectedType => do
  let .forallE _ domain _ _ ← whnf expectedType
    | throwError "expected an encoder function type"
  let alts ← alternativesFor domain recursiveCall
  elabTerm (← `(fun $alts:matchAlt*)) (some expectedType)

elab "certifiedMatch% " value:term " using " recursiveCall:term : term => do
  let expr ← elabTerm value none
  let alts ← alternativesFor (← inferType expr) recursiveCall
  elabTerm (← `(match $value:term with $alts:matchAlt*)) (some (mkConst ``Raw))

/-- Generate the encoder, `.Laws`, and `.certified`. Ordinary binders are
fixed parameters; binders following `indexed` are intrinsic indices that
recursive constructors may change. All generated names belong to the encoder.
-/
syntax (name := deriveCertifiedEncoding)
  (docComment)? "derive_certified_encoding " ident bracketedBinder* " indexed " bracketedBinder*
  " : " term : command

elab_rules : command
  | `($[$doc:docComment]? derive_certified_encoding $name:ident $params:bracketedBinder*
      indexed $indices:bracketedBinder* : $type:term) => do
    let mut paramNames : Array (TSyntax `term) := #[]
    for param in params do
      unless param.raw.getKind == ``Lean.Parser.Term.explicitBinder do
        throwError "fixed parameters must use explicit typed binders"
      for id in param.raw[1].getArgs do
        unless id.isIdent do throwError "expected named fixed parameter"
        paramNames := paramNames.push ⟨id⟩
    let call ← `($name $paramNames*)
    let lawsName := mkIdent (name.getId ++ `Laws)
    let witnessName := mkIdent (name.getId ++ `certified)
    let funIndices : TSyntaxArray ``funBinder := indices.map fun stx => ⟨stx.raw⟩
    let mut indexNames : Array (TSyntax `term) := #[]
    for binder in indices do
      for id in binder.raw[1].getArgs do
        unless id.isIdent do throwError "expected named index"
        indexNames := indexNames.push ⟨id⟩
    let savedEnv ← getEnv
    try
      elabCommand (← `($[$doc:docComment]? def $name $params* : ∀ $indices*, $type → Raw :=
      fun $funIndices* => certifiedFun% using $call))
      if (← get).messages.hasErrors then throwAbortCommand
      elabCommand (← `(def $lawsName $params* $indices* : Prop :=
      ∀ value : $type, $call value = certifiedMatch% value using $call))
      if (← get).messages.hasErrors then throwAbortCommand
      elabCommand (← `(def $witnessName $params* $indices* :
          CertifiedFieldEncoding $type $call (@$lawsName $paramNames* $indexNames*) :=
      CertifiedFieldEncoding.ofLaws $call (by
        intro value
        cases value <;> rfl)))
      if (← get).messages.hasErrors then throwAbortCommand
      let fullName ← resolveGlobalConstNoOverload witnessName
      modifyEnv fun env => certifiedEncoders.addEntry env fullName
    catch ex =>
      setEnv savedEnv
      throw ex

end Lax58.CertifiedDerivationElab
end

-- Lax58.WordArena
noncomputable section
namespace Lax58.WordArena
end Lax58.WordArena

namespace Lax58.WordArena.WordImage
end Lax58.WordArena.WordImage

namespace Lax58.WordArena.encodeInto
end Lax58.WordArena.encodeInto

namespace Lax58.WordArena.WordImage.ChildAddress
end Lax58.WordArena.WordImage.ChildAddress

namespace Lax58.WordArena.WordImage.ReachableFrom
end Lax58.WordArena.WordImage.ReachableFrom

namespace Lax58.WordArena.WordImage.Represents
end Lax58.WordArena.WordImage.Represents
end

-- Lax53.StructuralRepresentations
noncomputable section
namespace Lax53.StructuralRepresentations.treeStructure
end Lax53.StructuralRepresentations.treeStructure

namespace Lax53.StructuralRepresentations

open FirstOrder

open FirstOrder.Language

open Lax52.MSOSyntax

open Lax53.RankedTree

open Lax53.TreeStructure

open Lax53.ValueTranslations

open Lax58.StructuralPresentation

open Lax58.StructuralPresentation.Presentation

open Lax58.StructuralCombinators

open Lax58.CertifiedDerivation

universe u

-- Expanded from Lax58.CertifiedDerivationElab.deriveCertifiedEncoding
noncomputable def _root_.Lax53.StructuralRepresentations.termStructure.match_1.{u_1} :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    (l : Nat) →
      (motive :
          FirstOrder.Language.Functions.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              l →
            Sort u_1) →
        (_f :
            FirstOrder.Language.Functions.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              l) →
          motive _f :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) (l : Nat)
      (motive :
        FirstOrder.Language.Functions.{0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            l →
          Sort u_1)
      (_f :
        FirstOrder.Language.Functions.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          l) =>
    @False.elim.{u_1} (motive _f)
      (Empty.casesOn.{0}
        (fun
            (x :
              FirstOrder.Language.Functions.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                l) =>
          False)
        _f)

noncomputable def _root_.Lax53.StructuralRepresentations.termStructure.match_3.{u_1} :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {n : Nat} →
      (motive :
          FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n) →
            Sort u_1) →
        (x :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n)) →
          (h_1 :
              (a : Fin n) →
                motive
                  (@FirstOrder.Language.Term.var.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n) a)) →
            (h_2 :
                (l : Nat) →
                  (_f :
                      FirstOrder.Language.Functions.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        l) →
                    (_ts :
                        Fin l →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) →
                      motive
                        (@FirstOrder.Language.Term.func.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n) l _f _ts)) →
              motive x :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n : Nat}
      (motive :
        FirstOrder.Language.Term.{0, 0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            (Fin n) →
          Sort u_1)
      (x :
        FirstOrder.Language.Term.{0, 0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (Fin n))
      (h_1 :
        (a : Fin n) →
          motive
            (@FirstOrder.Language.Term.var.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n) a))
      (h_2 :
        (l : Nat) →
          (_f :
              FirstOrder.Language.Functions.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                l) →
            (_ts :
                Fin l →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n)) →
              motive
                (@FirstOrder.Language.Term.func.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n) l _f _ts)) =>
    @FirstOrder.Language.Term.casesOn.{u_1, 0, 0, 0}
      (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (Fin n)
      (fun
          (x :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n)) =>
        motive x)
      x (fun (a : Fin n) => h_1 a)
      fun {l : Nat}
        (_f :
          FirstOrder.Language.Functions.{0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            l)
        (_ts :
          Fin l →
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n)) =>
      h_2 l _f _ts

noncomputable def _root_.Lax53.StructuralRepresentations.termStructure :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {n : Nat} →
      FirstOrder.Language.Term.{0, 0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (Fin n) →
        Lax58.StructuralPresentation.Raw :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n : Nat}
      (x :
        FirstOrder.Language.Term.{0, 0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (Fin n)) =>
    @Lax53.StructuralRepresentations.termStructure.match_3.{1} alphabet n
      (fun
          (x :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n)) =>
        Lax58.StructuralPresentation.Raw)
      x
      (fun (a : Fin n) =>
        Lax58.StructuralCombinators.Raw.constructor "var"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin n)
              (fun (i : Fin n) => Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
              (∀ (i : Fin n),
                @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                  (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i)))
              ((fun (a : Fin n) => Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin n) a) a)
            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
      fun (l : Nat)
        (_f :
          FirstOrder.Language.Functions.{0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            l)
        (_ts :
          Fin l →
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n)) =>
      Lax53.StructuralRepresentations.termStructure.match_1.{1} alphabet l
        (fun
            (_f :
              FirstOrder.Language.Functions.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                l) =>
          Lax58.StructuralPresentation.Raw)
        _f

noncomputable def _root_.Lax53.StructuralRepresentations.termStructure.Laws :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) → {n : Nat} → Prop :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n : Nat} =>
    ∀
      (value :
        FirstOrder.Language.Term.{0, 0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (Fin n)),
      @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.termStructure alphabet n value)
        (@Lax53.StructuralRepresentations.termStructure.match_3.{1} alphabet n
          (fun
              (value :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n)) =>
            Lax58.StructuralPresentation.Raw)
          value
          (fun (a : Fin n) =>
            Lax58.StructuralCombinators.Raw.constructor "var"
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin n)
                  (fun (i : Fin n) => Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                  (∀ (i : Fin n),
                    @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i)))
                  ((fun (a : Fin n) => Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin n) a) a)
                (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
          fun (l : Nat)
            (_f :
              FirstOrder.Language.Functions.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                l)
            (_ts :
              Fin l →
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n)) =>
          Lax53.StructuralRepresentations.termStructure.match_1.{1} alphabet l
            (fun
                (_f :
                  FirstOrder.Language.Functions.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    l) =>
              Lax58.StructuralPresentation.Raw)
            _f)

theorem _root_.Lax53.StructuralRepresentations.termStructure.certified._proof_1 :
  ∀ (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n : Nat}
    (value :
      FirstOrder.Language.Term.{0, 0, 0}
        (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
        (Fin n)),
    @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.termStructure alphabet n value)
      (@Lax53.StructuralRepresentations.termStructure.match_3.{1} alphabet n
        (fun
            (value :
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n)) =>
          Lax58.StructuralPresentation.Raw)
        value
        (fun (a : Fin n) =>
          Lax58.StructuralCombinators.Raw.constructor "var"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin n)
                (fun (i : Fin n) => Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                (∀ (i : Fin n),
                  @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i)))
                (Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin n) a)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
        fun (l : Nat)
          (_f :
            FirstOrder.Language.Functions.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              l)
          (_ts :
            Fin l →
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n)) =>
        Lax53.StructuralRepresentations.termStructure.match_1.{1} alphabet l
          (fun
              (_f :
                FirstOrder.Language.Functions.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  l) =>
            Lax58.StructuralPresentation.Raw)
          _f) :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n : Nat}
      (value :
        FirstOrder.Language.Term.{0, 0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (Fin n)) =>
    @FirstOrder.Language.Term.casesOn.{0, 0, 0, 0}
      (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (Fin n)
      (fun
          (t :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n)) =>
        ∀
          (h :
            @Eq.{1}
              (FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
              value t),
          @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.termStructure alphabet n value)
            (@Lax53.StructuralRepresentations.termStructure.match_3.{1} alphabet n
              (fun
                  (value :
                    FirstOrder.Language.Term.{0, 0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (Fin n)) =>
                Lax58.StructuralPresentation.Raw)
              value
              (fun (a : Fin n) =>
                Lax58.StructuralCombinators.Raw.constructor "var"
                  (@List.cons.{0} Lax58.StructuralPresentation.Raw
                    (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin n)
                      (fun (i : Fin n) => Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                      (∀ (i : Fin n),
                        @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                          (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i)))
                      ((fun (a : Fin n) => Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin n) a) a)
                    (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
              fun (l : Nat)
                (_f :
                  FirstOrder.Language.Functions.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    l)
                (_ts :
                  Fin l →
                    FirstOrder.Language.Term.{0, 0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (Fin n)) =>
              Lax53.StructuralRepresentations.termStructure.match_1.{1} alphabet l
                (fun
                    (_f :
                      FirstOrder.Language.Functions.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        l) =>
                  Lax58.StructuralPresentation.Raw)
                _f))
      value
      (fun (a : Fin n)
          (h :
            @Eq.{1}
              (FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
              value
              (@FirstOrder.Language.Term.var.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n) a)) =>
        @Eq.ndrec.{0, 1}
          (FirstOrder.Language.Term.{0, 0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            (Fin n))
          (@FirstOrder.Language.Term.var.{0, 0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            (Fin n) a)
          (fun
              (value :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n)) =>
            @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.termStructure alphabet n value)
              (@Lax53.StructuralRepresentations.termStructure.match_3.{1} alphabet n
                (fun
                    (value :
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n)) =>
                  Lax58.StructuralPresentation.Raw)
                value
                (fun (a : Fin n) =>
                  Lax58.StructuralCombinators.Raw.constructor "var"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin n)
                        (fun (i : Fin n) => Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                        (∀ (i : Fin n),
                          @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                            (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i)))
                        ((fun (a : Fin n) => Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin n) a) a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                fun (l : Nat)
                  (_f :
                    FirstOrder.Language.Functions.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      l)
                  (_ts :
                    Fin l →
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n)) =>
                Lax53.StructuralRepresentations.termStructure.match_1.{1} alphabet l
                  (fun
                      (_f :
                        FirstOrder.Language.Functions.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          l) =>
                    Lax58.StructuralPresentation.Raw)
                  _f))
          (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
            (@Lax53.StructuralRepresentations.termStructure alphabet n
              (@FirstOrder.Language.Term.var.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n) a)))
          value
          (@Eq.symm.{1}
            (FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n))
            value
            (@FirstOrder.Language.Term.var.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n) a)
            h))
      (fun {l : Nat}
          (_f :
            FirstOrder.Language.Functions.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              l)
          (_ts :
            Fin l →
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
          (h :
            @Eq.{1}
              (FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
              value
              (@FirstOrder.Language.Term.func.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n) l _f _ts)) =>
        @Eq.ndrec.{0, 1}
          (FirstOrder.Language.Term.{0, 0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            (Fin n))
          (@FirstOrder.Language.Term.func.{0, 0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            (Fin n) l _f _ts)
          (fun
              (value :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n)) =>
            @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.termStructure alphabet n value)
              (@Lax53.StructuralRepresentations.termStructure.match_3.{1} alphabet n
                (fun
                    (value :
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n)) =>
                  Lax58.StructuralPresentation.Raw)
                value
                (fun (a : Fin n) =>
                  Lax58.StructuralCombinators.Raw.constructor "var"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin n)
                        (fun (i : Fin n) => Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                        (∀ (i : Fin n),
                          @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i))
                            (Lax58.StructuralPresentation.Raw.nat (@Fin.val n i)))
                        ((fun (a : Fin n) => Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin n) a) a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                fun (l : Nat)
                  (_f :
                    FirstOrder.Language.Functions.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      l)
                  (_ts :
                    Fin l →
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n)) =>
                Lax53.StructuralRepresentations.termStructure.match_1.{1} alphabet l
                  (fun
                      (_f :
                        FirstOrder.Language.Functions.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          l) =>
                    Lax58.StructuralPresentation.Raw)
                  _f))
          (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
            (@Lax53.StructuralRepresentations.termStructure alphabet n
              (@FirstOrder.Language.Term.func.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n) l _f _ts)))
          value
          (@Eq.symm.{1}
            (FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n))
            value
            (@FirstOrder.Language.Term.func.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n) l _f _ts)
            h))
      (@Eq.refl.{1}
        (FirstOrder.Language.Term.{0, 0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (Fin n))
        value)

noncomputable def _root_.Lax53.StructuralRepresentations.termStructure.certified :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {n : Nat} →
      Lax58.CertifiedDerivation.CertifiedFieldEncoding.{0}
        (FirstOrder.Language.Term.{0, 0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (Fin n))
        (@Lax53.StructuralRepresentations.termStructure alphabet n)
        (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n) :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n : Nat} =>
    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.ofLaws.{0}
      (FirstOrder.Language.Term.{0, 0, 0}
        (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
        (Fin n))
      (@Lax53.StructuralRepresentations.termStructure alphabet n)
      (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
      (@Lax53.StructuralRepresentations.termStructure.certified._proof_1 alphabet n)

-- Expanded from Lax58.CertifiedDerivationElab.deriveCertifiedEncoding
noncomputable def _root_.Lax53.StructuralRepresentations.relationStructure.match_1.{u_1} :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    (motive :
        (arity : Nat) →
          FirstOrder.Language.Relations.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              arity →
            Sort u_1) →
      (arity : Nat) →
        (x :
            FirstOrder.Language.Relations.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              arity) →
          (h_1 :
              (a :
                  Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
                motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Lax53.TreeStructure.TreeRelation.label.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) →
            (h_2 :
                (i :
                    Lax53.RankedTree.ChildIndex.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
                  motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Lax53.TreeStructure.TreeRelation.child.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)) →
              motive arity x :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode)
      (motive :
        (arity : Nat) →
          FirstOrder.Language.Relations.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              arity →
            Sort u_1)
      (arity : Nat)
      (x :
        FirstOrder.Language.Relations.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          arity)
      (h_1 :
        (a :
            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
          motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Lax53.TreeStructure.TreeRelation.label.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
      (h_2 :
        (i : Lax53.RankedTree.ChildIndex.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
          motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Lax53.TreeStructure.TreeRelation.child.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)) =>
    @Lax53.TreeStructure.TreeRelation.casesOn.{u_1, 0}
      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
      (fun (a : Nat)
          (x_1 :
            Lax53.TreeStructure.TreeRelation.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
              a) =>
        (h : @Eq.{1} Nat arity a) →
          (h :
              @HEq.{1}
                (FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  arity)
                x
                (Lax53.TreeStructure.TreeRelation.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                x_1) →
            motive arity x)
      arity x
      (fun
          (a :
            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (h : @Eq.{1} Nat arity (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
        @Eq.ndrec.{u_1, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (fun (arity : Nat) =>
            (x :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  arity) →
              (h :
                  @HEq.{1}
                    (FirstOrder.Language.Relations.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      arity)
                    x
                    (Lax53.TreeStructure.TreeRelation.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@Lax53.TreeStructure.TreeRelation.label.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) →
                motive arity x)
          (fun
              (x :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (h :
                @HEq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  x
                  (Lax53.TreeStructure.TreeRelation.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Lax53.TreeStructure.TreeRelation.label.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
            @Eq.ndrec.{u_1, 1}
              (FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Lax53.TreeStructure.TreeRelation.label.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
              (fun
                  (x :
                    FirstOrder.Language.Relations.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) x)
              (h_1 a) x
              (@Eq.symm.{1}
                (FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                x
                (@Lax53.TreeStructure.TreeRelation.label.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                (@eq_of_heq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  x
                  (@Lax53.TreeStructure.TreeRelation.label.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                  h)))
          arity (@Eq.symm.{1} Nat arity (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) h) x)
      (fun (i : Lax53.RankedTree.ChildIndex.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (h : @Eq.{1} Nat arity (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
        @Eq.ndrec.{u_1, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (fun (arity : Nat) =>
            (x :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  arity) →
              (h :
                  @HEq.{1}
                    (FirstOrder.Language.Relations.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      arity)
                    x
                    (Lax53.TreeStructure.TreeRelation.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Lax53.TreeStructure.TreeRelation.child.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)) →
                motive arity x)
          (fun
              (x :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (h :
                @HEq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  x
                  (Lax53.TreeStructure.TreeRelation.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Lax53.TreeStructure.TreeRelation.child.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)) =>
            @Eq.ndrec.{u_1, 1}
              (FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Lax53.TreeStructure.TreeRelation.child.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)
              (fun
                  (x :
                    FirstOrder.Language.Relations.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
                motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x)
              (h_2 i) x
              (@Eq.symm.{1}
                (FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                x
                (@Lax53.TreeStructure.TreeRelation.child.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)
                (@eq_of_heq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  x
                  (@Lax53.TreeStructure.TreeRelation.child.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)
                  h)))
          arity (@Eq.symm.{1} Nat arity (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h) x)
      (@Eq.refl.{1} Nat arity)
      (@HEq.refl.{1}
        (FirstOrder.Language.Relations.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          arity)
        x)

noncomputable def _root_.Lax53.StructuralRepresentations.relationStructure :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {arity : Nat} →
      FirstOrder.Language.Relations.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          arity →
        Lax58.StructuralPresentation.Raw :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {arity : Nat}
      (x :
        FirstOrder.Language.Relations.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          arity) =>
    Lax53.StructuralRepresentations.relationStructure.match_1.{1} alphabet
      (fun (arity : Nat)
          (x :
            FirstOrder.Language.Relations.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              arity) =>
        Lax58.StructuralPresentation.Raw)
      arity x
      (fun
          (a :
            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
        Lax58.StructuralCombinators.Raw.constructor "label"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin (@List.length.{0} Nat alphabet))
              (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
              (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                @Eq.{1} Lax58.StructuralPresentation.Raw
                  (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                  (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
              ((fun
                    (a :
                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                  Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                a)
              a)
            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
      fun (i : Lax53.RankedTree.ChildIndex.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
      Lax58.StructuralCombinators.Raw.constructor "child"
        (@List.cons.{0} Lax58.StructuralPresentation.Raw
          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
            (@Subtype.{1} Nat fun (i : Nat) =>
              @Exists.{1}
                (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                fun
                  (a :
                    Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                @LT.lt.{0} Nat instLTNat i
                  (Lax53.RankedTree.RankedAlphabet.rank.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
            (fun
                (x :
                  @Subtype.{1} Nat fun (i : Nat) =>
                    @Exists.{1}
                      (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      fun
                        (a :
                          Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                      @LT.lt.{0} Nat instLTNat i
                        (Lax53.RankedTree.RankedAlphabet.rank.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
              Lax58.StructuralPresentation.Raw.nat
                (@Subtype.val.{1} Nat
                  (fun (i : Nat) =>
                    @Exists.{1}
                      (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      fun
                        (a :
                          Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                      @LT.lt.{0} Nat instLTNat i
                        (Lax53.RankedTree.RankedAlphabet.rank.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                  x))
            (∀ (n : Nat),
              @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                (Lax58.StructuralPresentation.Raw.nat n))
            ((fun
                  (i :
                    Lax53.RankedTree.ChildIndex.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.subtype.{0} Nat Lax58.StructuralPresentation.Raw.nat
                  (∀ (n : Nat),
                    @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                      (Lax58.StructuralPresentation.Raw.nat n))
                  Lax58.CertifiedDerivation.CertifiedFieldEncoding.nat fun (i : Nat) =>
                  @Exists.{1}
                    (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    fun
                      (a :
                        Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                    @LT.lt.{0} Nat instLTNat i
                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
              i)
            i)
          (@List.nil.{0} Lax58.StructuralPresentation.Raw))

noncomputable def _root_.Lax53.StructuralRepresentations.relationStructure.Laws :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) → {arity : Nat} → Prop :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {arity : Nat} =>
    ∀
      (value :
        FirstOrder.Language.Relations.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          arity),
      @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.relationStructure alphabet arity value)
        (Lax53.StructuralRepresentations.relationStructure.match_1.{1} alphabet
          (fun (arity : Nat)
              (value :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  arity) =>
            Lax58.StructuralPresentation.Raw)
          arity value
          (fun
              (a :
                Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
            Lax58.StructuralCombinators.Raw.constructor "label"
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin (@List.length.{0} Nat alphabet))
                  (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                    Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                  (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
                  ((fun
                        (a :
                          Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                    a)
                  a)
                (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
          fun
            (i :
              Lax53.RankedTree.ChildIndex.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
          Lax58.StructuralCombinators.Raw.constructor "child"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                (@Subtype.{1} Nat fun (i : Nat) =>
                  @Exists.{1}
                    (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    fun
                      (a :
                        Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                    @LT.lt.{0} Nat instLTNat i
                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                (fun
                    (x :
                      @Subtype.{1} Nat fun (i : Nat) =>
                        @Exists.{1}
                          (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          fun
                            (a :
                              Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                          @LT.lt.{0} Nat instLTNat i
                            (Lax53.RankedTree.RankedAlphabet.rank.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                  Lax58.StructuralPresentation.Raw.nat
                    (@Subtype.val.{1} Nat
                      (fun (i : Nat) =>
                        @Exists.{1}
                          (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          fun
                            (a :
                              Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                          @LT.lt.{0} Nat instLTNat i
                            (Lax53.RankedTree.RankedAlphabet.rank.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                      x))
                (∀ (n : Nat),
                  @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                    (Lax58.StructuralPresentation.Raw.nat n))
                ((fun
                      (i :
                        Lax53.RankedTree.ChildIndex.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.subtype.{0} Nat Lax58.StructuralPresentation.Raw.nat
                      (∀ (n : Nat),
                        @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                          (Lax58.StructuralPresentation.Raw.nat n))
                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.nat fun (i : Nat) =>
                      @Exists.{1}
                        (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        fun
                          (a :
                            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                        @LT.lt.{0} Nat instLTNat i
                          (Lax53.RankedTree.RankedAlphabet.rank.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                  i)
                i)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))

theorem _root_.Lax53.StructuralRepresentations.relationStructure.certified._proof_1 :
  ∀ (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {arity : Nat}
    (value :
      FirstOrder.Language.Relations.{0, 0}
        (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
        arity),
    @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.relationStructure alphabet arity value)
      (Lax53.StructuralRepresentations.relationStructure.match_1.{1} alphabet
        (fun (arity : Nat)
            (value :
              FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                arity) =>
          Lax58.StructuralPresentation.Raw)
        arity value
        (fun
            (a :
              Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
          Lax58.StructuralCombinators.Raw.constructor "label"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin (@List.length.{0} Nat alphabet))
                (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                  Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
                (Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet)) a)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
        fun
          (i : Lax53.RankedTree.ChildIndex.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
        Lax58.StructuralCombinators.Raw.constructor "child"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
              (@Subtype.{1} Nat fun (i : Nat) =>
                @Exists.{1}
                  (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  fun
                    (a :
                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                  @LT.lt.{0} Nat instLTNat i
                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
              (fun
                  (x :
                    @Subtype.{1} Nat fun (i : Nat) =>
                      @Exists.{1}
                        (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        fun
                          (a :
                            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                        @LT.lt.{0} Nat instLTNat i
                          (Lax53.RankedTree.RankedAlphabet.rank.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                Lax58.StructuralPresentation.Raw.nat
                  (@Subtype.val.{1} Nat
                    (fun (i : Nat) =>
                      @Exists.{1}
                        (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        fun
                          (a :
                            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                        @LT.lt.{0} Nat instLTNat i
                          (Lax53.RankedTree.RankedAlphabet.rank.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                    x))
              (∀ (n : Nat),
                @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                  (Lax58.StructuralPresentation.Raw.nat n))
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.subtype.{0} Nat Lax58.StructuralPresentation.Raw.nat
                (∀ (n : Nat),
                  @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                    (Lax58.StructuralPresentation.Raw.nat n))
                Lax58.CertifiedDerivation.CertifiedFieldEncoding.nat fun (i : Nat) =>
                @Exists.{1}
                  (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  fun
                    (a :
                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                  @LT.lt.{0} Nat instLTNat i
                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
              i)
            (@List.nil.{0} Lax58.StructuralPresentation.Raw))) :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {arity : Nat}
      (value :
        FirstOrder.Language.Relations.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          arity) =>
    @Lax53.TreeStructure.TreeRelation.casesOn.{0, 0}
      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
      (fun (a : Nat)
          (t :
            Lax53.TreeStructure.TreeRelation.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
              a) =>
        ∀ (h : @Eq.{1} Nat arity a)
          (h :
            @HEq.{1}
              (FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                arity)
              value
              (Lax53.TreeStructure.TreeRelation.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                a)
              t),
          @Eq.{1} Lax58.StructuralPresentation.Raw
            (@Lax53.StructuralRepresentations.relationStructure alphabet arity value)
            (Lax53.StructuralRepresentations.relationStructure.match_1.{1} alphabet
              (fun (arity : Nat)
                  (value :
                    FirstOrder.Language.Relations.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      arity) =>
                Lax58.StructuralPresentation.Raw)
              arity value
              (fun
                  (a :
                    Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                Lax58.StructuralCombinators.Raw.constructor "label"
                  (@List.cons.{0} Lax58.StructuralPresentation.Raw
                    (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin (@List.length.{0} Nat alphabet))
                      (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                        Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                      (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                        @Eq.{1} Lax58.StructuralPresentation.Raw
                          (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                          (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
                      ((fun
                            (a :
                              Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                          Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                        a)
                      a)
                    (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
              fun
                (i :
                  Lax53.RankedTree.ChildIndex.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
              Lax58.StructuralCombinators.Raw.constructor "child"
                (@List.cons.{0} Lax58.StructuralPresentation.Raw
                  (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                    (@Subtype.{1} Nat fun (i : Nat) =>
                      @Exists.{1}
                        (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        fun
                          (a :
                            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                        @LT.lt.{0} Nat instLTNat i
                          (Lax53.RankedTree.RankedAlphabet.rank.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                    (fun
                        (x :
                          @Subtype.{1} Nat fun (i : Nat) =>
                            @Exists.{1}
                              (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              fun
                                (a :
                                  Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                              @LT.lt.{0} Nat instLTNat i
                                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                      Lax58.StructuralPresentation.Raw.nat
                        (@Subtype.val.{1} Nat
                          (fun (i : Nat) =>
                            @Exists.{1}
                              (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              fun
                                (a :
                                  Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                              @LT.lt.{0} Nat instLTNat i
                                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                          x))
                    (∀ (n : Nat),
                      @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                        (Lax58.StructuralPresentation.Raw.nat n))
                    ((fun
                          (i :
                            Lax53.RankedTree.ChildIndex.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                        @Lax58.CertifiedDerivation.CertifiedFieldEncoding.subtype.{0} Nat
                          Lax58.StructuralPresentation.Raw.nat
                          (∀ (n : Nat),
                            @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                              (Lax58.StructuralPresentation.Raw.nat n))
                          Lax58.CertifiedDerivation.CertifiedFieldEncoding.nat fun (i : Nat) =>
                          @Exists.{1}
                            (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            fun
                              (a :
                                Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                            @LT.lt.{0} Nat instLTNat i
                              (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                      i)
                    i)
                  (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      arity value
      (fun
          (a :
            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (h : @Eq.{1} Nat arity (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
        @Eq.ndrec.{0, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (fun {arity : Nat} =>
            ∀
              (value :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  arity)
              (h :
                @HEq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    arity)
                  value
                  (Lax53.TreeStructure.TreeRelation.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Lax53.TreeStructure.TreeRelation.label.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.relationStructure alphabet arity value)
                (Lax53.StructuralRepresentations.relationStructure.match_1.{1} alphabet
                  (fun (arity : Nat)
                      (value :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          arity) =>
                    Lax58.StructuralPresentation.Raw)
                  arity value
                  (fun
                      (a :
                        Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                    Lax58.StructuralCombinators.Raw.constructor "label"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin (@List.length.{0} Nat alphabet))
                          (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                            Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                          (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                            @Eq.{1} Lax58.StructuralPresentation.Raw
                              (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                              (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
                          ((fun
                                (a :
                                  Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                              Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                            a)
                          a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun
                    (i :
                      Lax53.RankedTree.ChildIndex.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                  Lax58.StructuralCombinators.Raw.constructor "child"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                        (@Subtype.{1} Nat fun (i : Nat) =>
                          @Exists.{1}
                            (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            fun
                              (a :
                                Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                            @LT.lt.{0} Nat instLTNat i
                              (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                        (fun
                            (x :
                              @Subtype.{1} Nat fun (i : Nat) =>
                                @Exists.{1}
                                  (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  fun
                                    (a :
                                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                          Lax58.StructuralPresentation.Raw.nat
                            (@Subtype.val.{1} Nat
                              (fun (i : Nat) =>
                                @Exists.{1}
                                  (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  fun
                                    (a :
                                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                              x))
                        (∀ (n : Nat),
                          @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                            (Lax58.StructuralPresentation.Raw.nat n))
                        ((fun
                              (i :
                                Lax53.RankedTree.ChildIndex.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                            @Lax58.CertifiedDerivation.CertifiedFieldEncoding.subtype.{0} Nat
                              Lax58.StructuralPresentation.Raw.nat
                              (∀ (n : Nat),
                                @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                                  (Lax58.StructuralPresentation.Raw.nat n))
                              Lax58.CertifiedDerivation.CertifiedFieldEncoding.nat fun (i : Nat) =>
                              @Exists.{1}
                                (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                fun
                                  (a :
                                    Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                @LT.lt.{0} Nat instLTNat i
                                  (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                          i)
                        i)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (value :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (h :
                @HEq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  value
                  (Lax53.TreeStructure.TreeRelation.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Lax53.TreeStructure.TreeRelation.label.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
            @Eq.ndrec.{0, 1}
              (FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Lax53.TreeStructure.TreeRelation.label.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
              (fun
                  (value :
                    FirstOrder.Language.Relations.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                @Eq.{1} Lax58.StructuralPresentation.Raw
                  (@Lax53.StructuralRepresentations.relationStructure alphabet
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) value)
                  (Lax53.StructuralRepresentations.relationStructure.match_1.{1} alphabet
                    (fun (arity : Nat)
                        (value :
                          FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            arity) =>
                      Lax58.StructuralPresentation.Raw)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) value
                    (fun
                        (a :
                          Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                      Lax58.StructuralCombinators.Raw.constructor "label"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (Fin (@List.length.{0} Nat alphabet))
                            (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                              Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                            (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
                            ((fun
                                  (a :
                                    Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                              a)
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                    fun
                      (i :
                        Lax53.RankedTree.ChildIndex.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                    Lax58.StructuralCombinators.Raw.constructor "child"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (@Subtype.{1} Nat fun (i : Nat) =>
                            @Exists.{1}
                              (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              fun
                                (a :
                                  Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                              @LT.lt.{0} Nat instLTNat i
                                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                          (fun
                              (x :
                                @Subtype.{1} Nat fun (i : Nat) =>
                                  @Exists.{1}
                                    (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    fun
                                      (a :
                                        Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                    @LT.lt.{0} Nat instLTNat i
                                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                            Lax58.StructuralPresentation.Raw.nat
                              (@Subtype.val.{1} Nat
                                (fun (i : Nat) =>
                                  @Exists.{1}
                                    (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    fun
                                      (a :
                                        Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                    @LT.lt.{0} Nat instLTNat i
                                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                                x))
                          (∀ (n : Nat),
                            @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                              (Lax58.StructuralPresentation.Raw.nat n))
                          ((fun
                                (i :
                                  Lax53.RankedTree.ChildIndex.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                              @Lax58.CertifiedDerivation.CertifiedFieldEncoding.subtype.{0} Nat
                                Lax58.StructuralPresentation.Raw.nat
                                (∀ (n : Nat),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                                    (Lax58.StructuralPresentation.Raw.nat n))
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.nat fun (i : Nat) =>
                                @Exists.{1}
                                  (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  fun
                                    (a :
                                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                            i)
                          i)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.relationStructure alphabet
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Lax53.TreeStructure.TreeRelation.label.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)))
              value
              (@Eq.symm.{1}
                (FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                value
                (@Lax53.TreeStructure.TreeRelation.label.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                (@eq_of_heq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  value
                  (@Lax53.TreeStructure.TreeRelation.label.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                  h)))
          arity (@Eq.symm.{1} Nat arity (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) h) value)
      (fun (i : Lax53.RankedTree.ChildIndex.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (h : @Eq.{1} Nat arity (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
        @Eq.ndrec.{0, 1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (fun {arity : Nat} =>
            ∀
              (value :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  arity)
              (h :
                @HEq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    arity)
                  value
                  (Lax53.TreeStructure.TreeRelation.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Lax53.TreeStructure.TreeRelation.child.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.relationStructure alphabet arity value)
                (Lax53.StructuralRepresentations.relationStructure.match_1.{1} alphabet
                  (fun (arity : Nat)
                      (value :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          arity) =>
                    Lax58.StructuralPresentation.Raw)
                  arity value
                  (fun
                      (a :
                        Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                    Lax58.StructuralCombinators.Raw.constructor "label"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin (@List.length.{0} Nat alphabet))
                          (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                            Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                          (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                            @Eq.{1} Lax58.StructuralPresentation.Raw
                              (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                              (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
                          ((fun
                                (a :
                                  Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                              Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                            a)
                          a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun
                    (i :
                      Lax53.RankedTree.ChildIndex.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                  Lax58.StructuralCombinators.Raw.constructor "child"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                        (@Subtype.{1} Nat fun (i : Nat) =>
                          @Exists.{1}
                            (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            fun
                              (a :
                                Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                            @LT.lt.{0} Nat instLTNat i
                              (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                        (fun
                            (x :
                              @Subtype.{1} Nat fun (i : Nat) =>
                                @Exists.{1}
                                  (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  fun
                                    (a :
                                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                          Lax58.StructuralPresentation.Raw.nat
                            (@Subtype.val.{1} Nat
                              (fun (i : Nat) =>
                                @Exists.{1}
                                  (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  fun
                                    (a :
                                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                              x))
                        (∀ (n : Nat),
                          @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                            (Lax58.StructuralPresentation.Raw.nat n))
                        ((fun
                              (i :
                                Lax53.RankedTree.ChildIndex.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                            @Lax58.CertifiedDerivation.CertifiedFieldEncoding.subtype.{0} Nat
                              Lax58.StructuralPresentation.Raw.nat
                              (∀ (n : Nat),
                                @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                                  (Lax58.StructuralPresentation.Raw.nat n))
                              Lax58.CertifiedDerivation.CertifiedFieldEncoding.nat fun (i : Nat) =>
                              @Exists.{1}
                                (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                fun
                                  (a :
                                    Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                @LT.lt.{0} Nat instLTNat i
                                  (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                          i)
                        i)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (value :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (h :
                @HEq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  value
                  (Lax53.TreeStructure.TreeRelation.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Lax53.TreeStructure.TreeRelation.child.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)) =>
            @Eq.ndrec.{0, 1}
              (FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Lax53.TreeStructure.TreeRelation.child.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)
              (fun
                  (value :
                    FirstOrder.Language.Relations.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
                @Eq.{1} Lax58.StructuralPresentation.Raw
                  (@Lax53.StructuralRepresentations.relationStructure alphabet
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) value)
                  (Lax53.StructuralRepresentations.relationStructure.match_1.{1} alphabet
                    (fun (arity : Nat)
                        (value :
                          FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            arity) =>
                      Lax58.StructuralPresentation.Raw)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) value
                    (fun
                        (a :
                          Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                      Lax58.StructuralCombinators.Raw.constructor "label"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (Fin (@List.length.{0} Nat alphabet))
                            (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                              Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                            (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
                            ((fun
                                  (a :
                                    Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                              a)
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                    fun
                      (i :
                        Lax53.RankedTree.ChildIndex.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                    Lax58.StructuralCombinators.Raw.constructor "child"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (@Subtype.{1} Nat fun (i : Nat) =>
                            @Exists.{1}
                              (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              fun
                                (a :
                                  Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                              @LT.lt.{0} Nat instLTNat i
                                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                          (fun
                              (x :
                                @Subtype.{1} Nat fun (i : Nat) =>
                                  @Exists.{1}
                                    (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    fun
                                      (a :
                                        Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                    @LT.lt.{0} Nat instLTNat i
                                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                            Lax58.StructuralPresentation.Raw.nat
                              (@Subtype.val.{1} Nat
                                (fun (i : Nat) =>
                                  @Exists.{1}
                                    (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    fun
                                      (a :
                                        Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                    @LT.lt.{0} Nat instLTNat i
                                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                                x))
                          (∀ (n : Nat),
                            @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                              (Lax58.StructuralPresentation.Raw.nat n))
                          ((fun
                                (i :
                                  Lax53.RankedTree.ChildIndex.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                              @Lax58.CertifiedDerivation.CertifiedFieldEncoding.subtype.{0} Nat
                                Lax58.StructuralPresentation.Raw.nat
                                (∀ (n : Nat),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat n)
                                    (Lax58.StructuralPresentation.Raw.nat n))
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.nat fun (i : Nat) =>
                                @Exists.{1}
                                  (Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  fun
                                    (a :
                                      Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a))
                            i)
                          i)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.relationStructure alphabet
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Lax53.TreeStructure.TreeRelation.child.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)))
              value
              (@Eq.symm.{1}
                (FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                value
                (@Lax53.TreeStructure.TreeRelation.child.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)
                (@eq_of_heq.{1}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  value
                  (@Lax53.TreeStructure.TreeRelation.child.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) i)
                  h)))
          arity (@Eq.symm.{1} Nat arity (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h) value)
      (@Eq.refl.{1} Nat arity)
      (@HEq.refl.{1}
        (FirstOrder.Language.Relations.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          arity)
        value)

noncomputable def _root_.Lax53.StructuralRepresentations.relationStructure.certified :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {arity : Nat} →
      Lax58.CertifiedDerivation.CertifiedFieldEncoding.{0}
        (FirstOrder.Language.Relations.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          arity)
        (@Lax53.StructuralRepresentations.relationStructure alphabet arity)
        (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet arity) :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {arity : Nat} =>
    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.ofLaws.{0}
      (FirstOrder.Language.Relations.{0, 0}
        (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
        arity)
      (@Lax53.StructuralRepresentations.relationStructure alphabet arity)
      (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet arity)
      (@Lax53.StructuralRepresentations.relationStructure.certified._proof_1 alphabet arity)

-- Expanded from Lax58.CertifiedDerivationElab.deriveCertifiedEncoding
noncomputable def _root_.Lax53.StructuralRepresentations.formulaStructure.match_1.{u_1} :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    (motive :
        (m n : Nat) →
          Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m →
            Sort u_1) →
      (m n : Nat) →
        (x :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m) →
          (h_1 :
              (m n : Nat) →
                motive m n
                  (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)) →
            (h_2 :
                (m n : Nat) →
                  (a a_1 :
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n)) →
                    motive m n
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_1)) →
              (h_3 :
                  (m n k : Nat) →
                    (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k) →
                      (a_1 :
                          Fin k →
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) →
                        motive m n
                          (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n m k a a_1)) →
                (h_4 :
                    (m n : Nat) →
                      (a :
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) →
                        (a_1 : Fin m) →
                          motive m n
                            (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m a a_1)) →
                  (h_5 :
                      (m n : Nat) →
                        (a a_1 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) →
                          motive m n
                            (@Lax52.MSOSyntax.Formula.or.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m a a_1)) →
                    (h_6 :
                        (m n : Nat) →
                          (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) →
                            motive m n
                              (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m a)) →
                      (h_7 :
                          (m n : Nat) →
                            (a :
                                Lax52.MSOSyntax.Formula.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  m) →
                              motive m n
                                (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  n m a)) →
                        (h_8 :
                            (m n : Nat) →
                              (a :
                                  Lax52.MSOSyntax.Formula.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    n
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                motive m n
                                  (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    n m a)) →
                          motive m n x :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode)
      (motive :
        (m n : Nat) →
          Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m →
            Sort u_1)
      (m n : Nat)
      (x :
        Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m)
      (h_1 :
        (m n : Nat) →
          motive m n
            (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m))
      (h_2 :
        (m n : Nat) →
          (a a_1 :
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n)) →
            motive m n
              (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a a_1))
      (h_3 :
        (m n k : Nat) →
          (a :
              FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                k) →
            (a_1 :
                Fin k →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n)) →
              motive m n
                (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m k a a_1))
      (h_4 :
        (m n : Nat) →
          (a :
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n)) →
            (a_1 : Fin m) →
              motive m n
                (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m a a_1))
      (h_5 :
        (m n : Nat) →
          (a a_1 :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m) →
            motive m n
              (@Lax52.MSOSyntax.Formula.or.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a a_1))
      (h_6 :
        (m n : Nat) →
          (a :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m) →
            motive m n
              (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a))
      (h_7 :
        (m n : Nat) →
          (a :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                m) →
            motive m n
              (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a))
      (h_8 :
        (m n : Nat) →
          (a :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            motive m n
              (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a)) =>
    @Lax52.MSOSyntax.Formula.casesOn.{u_1, 0, 0}
      (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (fun (a a_1 : Nat)
          (x_1 :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              a a_1) =>
        (h : @Eq.{1} Nat n a) →
          (h : @Eq.{1} Nat m a_1) →
            (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  x
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    a a_1)
                  x_1) →
              motive m n x)
      n m x
      (fun {n_1 m_1 : Nat} (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{u_1, 1} Nat n
          (fun {n_2 : Nat} =>
            (h : @Eq.{1} Nat m m_1) →
              (h :
                  @HEq.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n_2 m_1)
                    (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n_2 m_1)) →
                motive m n x)
          (fun (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{u_1, 1} Nat m
              (fun {m_2 : Nat} =>
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)) →
                  motive m n x)
              (fun
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)) =>
                @Eq.ndrec.{u_1, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (fun
                      (x :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    motive m n x)
                  (h_1 m n) x
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      h)))
              m_1 h)
          n_1 h)
      (fun {n_1 m_1 : Nat}
          (a a_1 :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n_1))
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{u_1, 1} Nat n
          (fun {n_2 : Nat} =>
            (a a_2 :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n_2)) →
              (h : @Eq.{1} Nat m m_1) →
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1)
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1 a a_2)) →
                  motive m n x)
          (fun
              (a a_2 :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{u_1, 1} Nat m
              (fun {m_2 : Nat} =>
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 a a_2)) →
                  motive m n x)
              (fun
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)) =>
                @Eq.ndrec.{u_1, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a a_2)
                  (fun
                      (x :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    motive m n x)
                  (h_2 m n a a_2) x
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a a_2)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)
                      h)))
              m_1 h)
          n_1 h a a_1)
      (fun {n_1 m_1 k : Nat}
          (a :
            FirstOrder.Language.Relations.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              k)
          (a_1 :
            Fin k →
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n_1))
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{u_1, 1} Nat n
          (fun {n_2 : Nat} =>
            (a_2 :
                Fin k →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n_2)) →
              (h : @Eq.{1} Nat m m_1) →
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1)
                      (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1 k a a_2)) →
                  motive m n x)
          (fun
              (a_2 :
                Fin k →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n))
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{u_1, 1} Nat m
              (fun {m_2 : Nat} =>
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 k a a_2)) →
                  motive m n x)
              (fun
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m k a a_2)) =>
                @Eq.ndrec.{u_1, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m k a a_2)
                  (fun
                      (x :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    motive m n x)
                  (h_3 m n k a a_2) x
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m k a a_2)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m k a a_2)
                      h)))
              m_1 h)
          n_1 h a_1)
      (fun {n_1 m_1 : Nat}
          (a :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n_1))
          (a_1 : Fin m_1) (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{u_1, 1} Nat n
          (fun {n_2 : Nat} =>
            (a :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n_2)) →
              (h : @Eq.{1} Nat m m_1) →
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1)
                      (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1 a a_1)) →
                  motive m n x)
          (fun
              (a :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{u_1, 1} Nat m
              (fun {m_2 : Nat} =>
                (a_2 : Fin m_2) →
                  (h :
                      @HEq.{1}
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m)
                        x
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2)
                        (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2 a a_2)) →
                    motive m n x)
              (fun (a_2 : Fin m)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)) =>
                @Eq.ndrec.{u_1, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a a_2)
                  (fun
                      (x :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    motive m n x)
                  (h_4 m n a a_2) x
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a a_2)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)
                      h)))
              m_1 h a_1)
          n_1 h a)
      (fun {n_1 m_1 : Nat}
          (a a_1 :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n_1 m_1)
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{u_1, 1} Nat n
          (fun {n_2 : Nat} =>
            (a a_2 :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n_2 m_1) →
              (h : @Eq.{1} Nat m m_1) →
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1)
                      (@Lax52.MSOSyntax.Formula.or.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1 a a_2)) →
                  motive m n x)
          (fun
              (a a_2 :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m_1)
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{u_1, 1} Nat m
              (fun {m_2 : Nat} =>
                (a a_3 :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m_2) →
                  (h :
                      @HEq.{1}
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m)
                        x
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2)
                        (@Lax52.MSOSyntax.Formula.or.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2 a a_3)) →
                    motive m n x)
              (fun
                  (a a_3 :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.or.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_3)) =>
                @Eq.ndrec.{u_1, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.or.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a a_3)
                  (fun
                      (x :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    motive m n x)
                  (h_5 m n a a_3) x
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (@Lax52.MSOSyntax.Formula.or.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a a_3)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (@Lax52.MSOSyntax.Formula.or.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_3)
                      h)))
              m_1 h a a_2)
          n_1 h a a_1)
      (fun {n_1 m_1 : Nat}
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n_1 m_1)
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{u_1, 1} Nat n
          (fun {n_2 : Nat} =>
            (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n_2 m_1) →
              (h : @Eq.{1} Nat m m_1) →
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1)
                      (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1 a)) →
                  motive m n x)
          (fun
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m_1)
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{u_1, 1} Nat m
              (fun {m_2 : Nat} =>
                (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m_2) →
                  (h :
                      @HEq.{1}
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m)
                        x
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2)
                        (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2 a)) →
                    motive m n x)
              (fun
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)) =>
                @Eq.ndrec.{u_1, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a)
                  (fun
                      (x :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    motive m n x)
                  (h_6 m n a) x
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)
                      h)))
              m_1 h a)
          n_1 h a)
      (fun {n_1 m_1 : Nat}
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              m_1)
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{u_1, 1} Nat n
          (fun {n_2 : Nat} =>
            (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_2
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  m_1) →
              (h : @Eq.{1} Nat m m_1) →
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1)
                      (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1 a)) →
                  motive m n x)
          (fun
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  m_1)
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{u_1, 1} Nat m
              (fun {m_2 : Nat} =>
                (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      m_2) →
                  (h :
                      @HEq.{1}
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m)
                        x
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2)
                        (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2 a)) →
                    motive m n x)
              (fun
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      m)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)) =>
                @Eq.ndrec.{u_1, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a)
                  (fun
                      (x :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    motive m n x)
                  (h_7 m n a) x
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)
                      h)))
              m_1 h a)
          n_1 h a)
      (fun {n_1 m_1 : Nat}
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n_1
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{u_1, 1} Nat n
          (fun {n_2 : Nat} =>
            (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n_2
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              (h : @Eq.{1} Nat m m_1) →
                (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1)
                      (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n_2 m_1 a)) →
                  motive m n x)
          (fun
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{u_1, 1} Nat m
              (fun {m_2 : Nat} =>
                (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_2
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  (h :
                      @HEq.{1}
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m)
                        x
                        (Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2)
                        (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m_2 a)) →
                    motive m n x)
              (fun
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)) =>
                @Eq.ndrec.{u_1, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a)
                  (fun
                      (x :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    motive m n x)
                  (h_8 m n a) x
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    x
                    (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      x
                      (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)
                      h)))
              m_1 h a)
          n_1 h a)
      (@Eq.refl.{1} Nat n) (@Eq.refl.{1} Nat m)
      (@HEq.refl.{1}
        (Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m)
        x)

noncomputable def _root_.Lax53.StructuralRepresentations.formulaStructure._f :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {n m : Nat} →
      (x :
          Lax52.MSOSyntax.Formula.{0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            n m) →
        (f :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m x) →
          Lax58.StructuralPresentation.Raw :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n m : Nat}
      (x :
        Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m)
      (f :
        @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (fun {n m : Nat}
              (x :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m) =>
            Lax58.StructuralPresentation.Raw)
          n m x) =>
    Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
      (fun (m n : Nat)
          (x :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m) =>
        @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            (fun {n m : Nat}
                (x :
                  Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m) =>
              Lax58.StructuralPresentation.Raw)
            n m x →
          Lax58.StructuralPresentation.Raw)
      m n x
      (fun (m n : Nat)
          (x :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m
              (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m)) =>
        Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
      (fun (m n : Nat)
          (a a_1 :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n))
          (x :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m
              (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a a_1)) =>
        Lax58.StructuralCombinators.Raw.constructor "equal"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
              (FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
              (@Lax53.StructuralRepresentations.termStructure alphabet n)
              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
              ((fun (n m : Nat)
                    (a a_2 :
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n)) =>
                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                n m a a_1)
              a)
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                (FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                ((fun (n m : Nat)
                      (a a_2 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                  n m a a_1)
                a_1)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      (fun (m n k : Nat)
          (a :
            FirstOrder.Language.Relations.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              k)
          (a_1 :
            Fin k →
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
          (x :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m
              (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m k a a_1)) =>
        Lax58.StructuralCombinators.Raw.constructor "rel"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
              (FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                k)
              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
              ((fun (n m k : Nat)
                    (a :
                      FirstOrder.Language.Relations.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        k)
                    (a_2 :
                      Fin k →
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                n m k a a_1)
              a)
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                ((i : Fin k) →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n))
                (fun
                    (f :
                      (i : Fin k) →
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                  Lax58.StructuralCombinators.Raw.fields
                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                ((fun (n m k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_2 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                      (fun (i : Fin k) =>
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                      fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                  n m k a a_1)
                a_1)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      (fun (m n : Nat)
          (a :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n))
          (a_1 : Fin m)
          (x :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m
              (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a a_1)) =>
        Lax58.StructuralCombinators.Raw.constructor "mem"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
              (FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
              (@Lax53.StructuralRepresentations.termStructure alphabet n)
              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
              ((fun (n m : Nat)
                    (a :
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n))
                    (a_2 : Fin m) =>
                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                n m a a_1)
              a)
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                (∀ (i : Fin m),
                  @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                ((fun (n m : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_2 : Fin m) =>
                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                  n m a a_1)
                a_1)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      (fun (m n : Nat)
          (a a_1 :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m)
          (x :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m
              (@Lax52.MSOSyntax.Formula.or.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a a_1)) =>
        Lax58.StructuralCombinators.Raw.constructor "or"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw x.1.1
            (@List.cons.{0} Lax58.StructuralPresentation.Raw x.2.1 (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      (fun (m n : Nat)
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m)
          (x :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m
              (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a)) =>
        Lax58.StructuralCombinators.Raw.constructor "neg"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw x.1 (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
      (fun (m n : Nat)
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              m)
          (x :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m
              (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a)) =>
        Lax58.StructuralCombinators.Raw.constructor "exFO"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw x.1 (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
      (fun (m n : Nat)
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (x :
            @Lax52.MSOSyntax.Formula.below.{1, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (fun {n m : Nat}
                  (x :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              n m
              (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m a)) =>
        Lax58.StructuralCombinators.Raw.constructor "exSO"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw x.1 (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
      f

noncomputable def _root_.Lax53.StructuralRepresentations.formulaStructure :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {n m : Nat} →
      Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m →
        Lax58.StructuralPresentation.Raw :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n m : Nat}
      (x :
        Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m) =>
    @Lax52.MSOSyntax.Formula.brecOn.{1, 0, 0}
      (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (fun {n m : Nat}
          (x :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m) =>
        Lax58.StructuralPresentation.Raw)
      n m x (@Lax53.StructuralRepresentations.formulaStructure._f alphabet)

noncomputable def _root_.Lax53.StructuralRepresentations.formulaStructure.Laws :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) → {n m : Nat} → Prop :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n m : Nat} =>
    ∀
      (value :
        Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m),
      @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
        (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
          (fun (m n : Nat)
              (value :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m) =>
            Lax58.StructuralPresentation.Raw)
          m n value
          (fun (m n : Nat) =>
            Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
          (fun (m n : Nat)
              (a a_1 :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n)) =>
            Lax58.StructuralCombinators.Raw.constructor "equal"
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                  (FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n))
                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                  ((fun (n m : Nat)
                        (a a_2 :
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                    n m a a_1)
                  a)
                (@List.cons.{0} Lax58.StructuralPresentation.Raw
                  (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                    (FirstOrder.Language.Term.{0, 0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (Fin n))
                    (@Lax53.StructuralRepresentations.termStructure alphabet n)
                    (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                    ((fun (n m : Nat)
                          (a a_2 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                      n m a a_1)
                    a_1)
                  (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun (m n k : Nat)
              (a :
                FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  k)
              (a_1 :
                Fin k →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n)) =>
            Lax58.StructuralCombinators.Raw.constructor "rel"
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                  (FirstOrder.Language.Relations.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    k)
                  (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                  (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                  ((fun (n m k : Nat)
                        (a :
                          FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                        (a_2 :
                          Fin k →
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                      @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                    n m k a a_1)
                  a)
                (@List.cons.{0} Lax58.StructuralPresentation.Raw
                  (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                    ((i : Fin k) →
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n))
                    (fun
                        (f :
                          (i : Fin k) →
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                      Lax58.StructuralCombinators.Raw.fields
                        (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                          @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                    (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                    ((fun (n m k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_2 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                          (fun (i : Fin k) =>
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                          (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                      n m k a a_1)
                    a_1)
                  (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun (m n : Nat)
              (a :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
              (a_1 : Fin m) =>
            Lax58.StructuralCombinators.Raw.constructor "mem"
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                  (FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n))
                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                  ((fun (n m : Nat)
                        (a :
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                        (a_2 : Fin m) =>
                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                    n m a a_1)
                  a)
                (@List.cons.{0} Lax58.StructuralPresentation.Raw
                  (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                    (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                    (∀ (i : Fin m),
                      @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                        (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                    ((fun (n m : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_2 : Fin m) =>
                        Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                      n m a a_1)
                    a_1)
                  (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun (m n : Nat)
              (a a_1 :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m) =>
            Lax58.StructuralCombinators.Raw.constructor "or"
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                (@List.cons.{0} Lax58.StructuralPresentation.Raw
                  (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                  (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun (m n : Nat)
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m) =>
            Lax58.StructuralCombinators.Raw.constructor "neg"
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
          (fun (m n : Nat)
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  m) =>
            Lax58.StructuralCombinators.Raw.constructor "exFO"
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  m a)
                (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
          fun (m n : Nat)
            (a :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          Lax58.StructuralCombinators.Raw.constructor "exSO"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                a)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))

noncomputable def _root_.Lax53.StructuralRepresentations.formulaStructure._sunfold :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {n m : Nat} →
      Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m →
        Lax58.StructuralPresentation.Raw :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n m : Nat}
      (x :
        Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m) =>
    Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
      (fun (m n : Nat)
          (x :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m) =>
        Lax58.StructuralPresentation.Raw)
      m n x
      (fun (m n : Nat) =>
        Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
      (fun (m n : Nat)
          (a a_1 :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n)) =>
        Lax58.StructuralCombinators.Raw.constructor "equal"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
              (FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
              (@Lax53.StructuralRepresentations.termStructure alphabet n)
              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
              ((fun (n m : Nat)
                    (a a_2 :
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n)) =>
                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                n m a a_1)
              a)
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                (FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                ((fun (n m : Nat)
                      (a a_2 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                  n m a a_1)
                a_1)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      (fun (m n k : Nat)
          (a :
            FirstOrder.Language.Relations.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              k)
          (a_1 :
            Fin k →
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n)) =>
        Lax58.StructuralCombinators.Raw.constructor "rel"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
              (FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                k)
              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
              ((fun (n m k : Nat)
                    (a :
                      FirstOrder.Language.Relations.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        k)
                    (a_2 :
                      Fin k →
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                n m k a a_1)
              a)
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                ((i : Fin k) →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n))
                (fun
                    (f :
                      (i : Fin k) →
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                  Lax58.StructuralCombinators.Raw.fields
                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                ((fun (n m k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_2 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                      (fun (i : Fin k) =>
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                      fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                  n m k a a_1)
                a_1)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      (fun (m n : Nat)
          (a :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n))
          (a_1 : Fin m) =>
        Lax58.StructuralCombinators.Raw.constructor "mem"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
              (FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
              (@Lax53.StructuralRepresentations.termStructure alphabet n)
              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
              ((fun (n m : Nat)
                    (a :
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n))
                    (a_2 : Fin m) =>
                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                n m a a_1)
              a)
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                (∀ (i : Fin m),
                  @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                ((fun (n m : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_2 : Fin m) =>
                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                  n m a a_1)
                a_1)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      (fun (m n : Nat)
          (a a_1 :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m) =>
        Lax58.StructuralCombinators.Raw.constructor "or"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      (fun (m n : Nat)
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n m) =>
        Lax58.StructuralCombinators.Raw.constructor "neg"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
      (fun (m n : Nat)
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              m) =>
        Lax58.StructuralCombinators.Raw.constructor "exFO"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax53.StructuralRepresentations.formulaStructure alphabet
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              m a)
            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
      fun (m n : Nat)
        (a :
          Lax52.MSOSyntax.Formula.{0, 0}
            (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      Lax58.StructuralCombinators.Raw.constructor "exSO"
        (@List.cons.{0} Lax58.StructuralPresentation.Raw
          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            a)
          (@List.nil.{0} Lax58.StructuralPresentation.Raw))

theorem _root_.Lax53.StructuralRepresentations.formulaStructure.certified._proof_1 :
  ∀ (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n m : Nat}
    (value :
      Lax52.MSOSyntax.Formula.{0, 0}
        (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
        m),
    @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
        (fun (m n : Nat)
            (value :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m) =>
          Lax58.StructuralPresentation.Raw)
        m n value
        (fun (m n : Nat) =>
          Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
        (fun (m n : Nat)
            (a a_1 :
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n)) =>
          Lax58.StructuralCombinators.Raw.constructor "equal"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                (FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                (@Lax53.StructuralRepresentations.termStructure.certified alphabet n) a)
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                  (FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n))
                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                  (@Lax53.StructuralRepresentations.termStructure.certified alphabet n) a_1)
                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
        (fun (m n k : Nat)
            (a :
              FirstOrder.Language.Relations.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                k)
            (a_1 :
              Fin k →
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n)) =>
          Lax58.StructuralCombinators.Raw.constructor "rel"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                (FirstOrder.Language.Relations.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  k)
                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                (@Lax53.StructuralRepresentations.relationStructure.certified alphabet k) a)
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                  ((i : Fin k) →
                    FirstOrder.Language.Term.{0, 0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (Fin n))
                  (fun
                      (f :
                        (i : Fin k) →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.fields
                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                  (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                    (fun (i : Fin k) =>
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n))
                    (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                    (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n) fun (a : Fin k) =>
                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                  a_1)
                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
        (fun (m n : Nat)
            (a :
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n))
            (a_1 : Fin m) =>
          Lax58.StructuralCombinators.Raw.constructor "mem"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                (FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                (@Lax53.StructuralRepresentations.termStructure.certified alphabet n) a)
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                  (∀ (i : Fin m),
                    @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                  (Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m) a_1)
                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
        (fun (m n : Nat)
            (a a_1 :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m) =>
          Lax58.StructuralCombinators.Raw.constructor "or"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
        (fun (m n : Nat)
            (a :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m) =>
          Lax58.StructuralCombinators.Raw.constructor "neg"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
        (fun (m n : Nat)
            (a :
              Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                m) =>
          Lax58.StructuralCombinators.Raw.constructor "exFO"
            (@List.cons.{0} Lax58.StructuralPresentation.Raw
              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                m a)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
        fun (m n : Nat)
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
        Lax58.StructuralCombinators.Raw.constructor "exSO"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              a)
            (@List.nil.{0} Lax58.StructuralPresentation.Raw))) :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n m : Nat}
      (value :
        Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m) =>
    @Lax52.MSOSyntax.Formula.casesOn.{0, 0, 0}
      (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (fun (a a_1 : Nat)
          (t :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              a a_1) =>
        ∀ (h : @Eq.{1} Nat n a) (h : @Eq.{1} Nat m a_1)
          (h :
            @HEq.{1}
              (Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                n m)
              value
              (Lax52.MSOSyntax.Formula.{0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                a a_1)
              t),
          @Eq.{1} Lax58.StructuralPresentation.Raw (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
            (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
              (fun (m n : Nat)
                  (value :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralPresentation.Raw)
              m n value
              (fun (m n : Nat) =>
                Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
              (fun (m n : Nat)
                  (a a_2 :
                    FirstOrder.Language.Term.{0, 0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (Fin n)) =>
                Lax58.StructuralCombinators.Raw.constructor "equal"
                  (@List.cons.{0} Lax58.StructuralPresentation.Raw
                    (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                      (FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n))
                      (@Lax53.StructuralRepresentations.termStructure alphabet n)
                      (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                      ((fun (n m : Nat)
                            (a a_3 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                        n m a a_2)
                      a)
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                        (FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                        (@Lax53.StructuralRepresentations.termStructure alphabet n)
                        (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                        ((fun (n m : Nat)
                              (a a_3 :
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                            @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                          n m a a_2)
                        a_2)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun (m n k : Nat)
                  (a :
                    FirstOrder.Language.Relations.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      k)
                  (a_2 :
                    Fin k →
                      FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n)) =>
                Lax58.StructuralCombinators.Raw.constructor "rel"
                  (@List.cons.{0} Lax58.StructuralPresentation.Raw
                    (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                      (FirstOrder.Language.Relations.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        k)
                      (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                      (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                      ((fun (n m k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_3 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                        n m k a a_2)
                      a)
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                        ((i : Fin k) →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                        (fun
                            (f :
                              (i : Fin k) →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.fields
                            (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                              @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                        (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                        ((fun (n m k : Nat)
                              (a :
                                FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                              (a_3 :
                                Fin k →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                            @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                              (fun (i : Fin k) =>
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                              (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                              (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                          n m k a a_2)
                        a_2)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun (m n : Nat)
                  (a :
                    FirstOrder.Language.Term.{0, 0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (Fin n))
                  (a_2 : Fin m) =>
                Lax58.StructuralCombinators.Raw.constructor "mem"
                  (@List.cons.{0} Lax58.StructuralPresentation.Raw
                    (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                      (FirstOrder.Language.Term.{0, 0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        (Fin n))
                      (@Lax53.StructuralRepresentations.termStructure alphabet n)
                      (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                      ((fun (n m : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_3 : Fin m) =>
                          @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                        n m a a_2)
                      a)
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                        (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                        (∀ (i : Fin m),
                          @Eq.{1} Lax58.StructuralPresentation.Raw (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                        ((fun (n m : Nat)
                              (a :
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                              (a_3 : Fin m) =>
                            Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                          n m a a_2)
                        a_2)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun (m n : Nat)
                  (a a_2 :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralCombinators.Raw.constructor "or"
                  (@List.cons.{0} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_2)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun (m n : Nat)
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m) =>
                Lax58.StructuralCombinators.Raw.constructor "neg"
                  (@List.cons.{0} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                    (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
              (fun (m n : Nat)
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      m) =>
                Lax58.StructuralCombinators.Raw.constructor "exFO"
                  (@List.cons.{0} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      m a)
                    (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
              fun (m n : Nat)
                (a :
                  Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
              Lax58.StructuralCombinators.Raw.constructor "exSO"
                (@List.cons.{0} Lax58.StructuralPresentation.Raw
                  (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    a)
                  (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      n m value
      (fun {n_1 m_1 : Nat} (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{0, 1} Nat n
          (fun {n_2 : Nat} =>
            ∀ (h : @Eq.{1} Nat m m_1)
              (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  value
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)
                  (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                  (fun (m n : Nat)
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralPresentation.Raw)
                  m n value
                  (fun (m n : Nat) =>
                    Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                  (fun (m n : Nat)
                      (a a_1 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "equal"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a a_2 :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                            (@Lax53.StructuralRepresentations.termStructure alphabet n)
                            (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m : Nat)
                                  (a a_2 :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                                @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_1 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "rel"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                          (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                          (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                          ((fun (n m k : Nat)
                                (a :
                                  FirstOrder.Language.Relations.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    k)
                                (a_2 :
                                  Fin k →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                            n m k a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            ((i : Fin k) →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (fun
                                (f :
                                  (i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              Lax58.StructuralCombinators.Raw.fields
                                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                  @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                            (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m k : Nat)
                                  (a :
                                    FirstOrder.Language.Relations.{0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      k)
                                  (a_2 :
                                    Fin k →
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                  (fun (i : Fin k) =>
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m k a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_1 : Fin m) =>
                    Lax58.StructuralCombinators.Raw.constructor "mem"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (a_2 : Fin m) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                            (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (∀ (i : Fin m),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                            ((fun (n m : Nat)
                                  (a :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (a_2 : Fin m) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                              n m a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a a_1 :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "or"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "neg"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m) =>
                    Lax58.StructuralCombinators.Raw.constructor "exFO"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun (m n : Nat)
                    (a :
                      Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  Lax58.StructuralCombinators.Raw.constructor "exSO"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{0, 1} Nat m
              (fun {m_2 : Nat} =>
                ∀
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                    (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                      (fun (m n : Nat)
                          (value :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralPresentation.Raw)
                      m n value
                      (fun (m n : Nat) =>
                        Lax58.StructuralCombinators.Raw.constructor "falsum"
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                      (fun (m n : Nat)
                          (a a_1 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "equal"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a a_2 :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_2 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_1 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "rel"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                              ((fun (n m k : Nat)
                                    (a :
                                      FirstOrder.Language.Relations.{0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        k)
                                    (a_2 :
                                      Fin k →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                n m k a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                ((i : Fin k) →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (fun
                                    (f :
                                      (i : Fin k) →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  Lax58.StructuralCombinators.Raw.fields
                                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_2 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                      (fun (i : Fin k) =>
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                      fun (a : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m k a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_1 : Fin m) =>
                        Lax58.StructuralCombinators.Raw.constructor "mem"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n))
                                    (a_2 : Fin m) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (∀ (i : Fin m),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_2 : Fin m) =>
                                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                  n m a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a a_1 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "or"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "neg"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m) =>
                        Lax58.StructuralCombinators.Raw.constructor "exFO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      fun (m n : Nat)
                        (a :
                          Lax52.MSOSyntax.Formula.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      Lax58.StructuralCombinators.Raw.constructor "exSO"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)) =>
                @Eq.ndrec.{0, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (fun
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                        (fun (m n : Nat)
                            (value :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralPresentation.Raw)
                        m n value
                        (fun (m n : Nat) =>
                          Lax58.StructuralCombinators.Raw.constructor "falsum"
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                        (fun (m n : Nat)
                            (a a_1 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "equal"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_2 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  (FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m : Nat)
                                        (a a_2 :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_1 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "rel"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_2 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                  n m k a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  ((i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun
                                      (f :
                                        (i : Fin k) →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    Lax58.StructuralCombinators.Raw.fields
                                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m k : Nat)
                                        (a :
                                          FirstOrder.Language.Relations.{0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            k)
                                        (a_2 :
                                          Fin k →
                                            FirstOrder.Language.Term.{0, 0, 0}
                                              (Lax53.TreeStructure.treeSignature.{0}
                                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                              (Fin n)) =>
                                      @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                        (fun (i : Fin k) =>
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                        (fun (i : Fin k) =>
                                          @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                        fun (a : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m k a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_1 : Fin m) =>
                          Lax58.StructuralCombinators.Raw.constructor "mem"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_2 : Fin m) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                  (∀ (i : Fin m),
                                    @Eq.{1} Lax58.StructuralPresentation.Raw
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                  ((fun (n m : Nat)
                                        (a :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (a_2 : Fin m) =>
                                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                    n m a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a a_1 :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "or"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "neg"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m) =>
                          Lax58.StructuralCombinators.Raw.constructor "exFO"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        Lax58.StructuralCombinators.Raw.constructor "exSO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m
                      (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)))
                  value
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    value
                    (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (@Lax52.MSOSyntax.Formula.falsum.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      h)))
              m_1 h)
          n_1 h)
      (fun {n_1 m_1 : Nat}
          (a a_1 :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n_1))
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{0, 1} Nat n
          (fun {n_2 : Nat} =>
            ∀
              (a a_2 :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n_2))
              (h : @Eq.{1} Nat m m_1)
              (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  value
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)
                  (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1 a a_2)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                  (fun (m n : Nat)
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralPresentation.Raw)
                  m n value
                  (fun (m n : Nat) =>
                    Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                  (fun (m n : Nat)
                      (a a_3 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "equal"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a a_4 :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                            (@Lax53.StructuralRepresentations.termStructure alphabet n)
                            (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m : Nat)
                                  (a a_4 :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                                @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_3 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "rel"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                          (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                          (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                          ((fun (n m k : Nat)
                                (a :
                                  FirstOrder.Language.Relations.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    k)
                                (a_4 :
                                  Fin k →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                            n m k a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            ((i : Fin k) →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (fun
                                (f :
                                  (i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              Lax58.StructuralCombinators.Raw.fields
                                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                  @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                            (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m k : Nat)
                                  (a :
                                    FirstOrder.Language.Relations.{0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      k)
                                  (a_4 :
                                    Fin k →
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                  (fun (i : Fin k) =>
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m k a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_3 : Fin m) =>
                    Lax58.StructuralCombinators.Raw.constructor "mem"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (a_4 : Fin m) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                            (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (∀ (i : Fin m),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                            ((fun (n m : Nat)
                                  (a :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (a_4 : Fin m) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                              n m a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a a_3 :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "or"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "neg"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m) =>
                    Lax58.StructuralCombinators.Raw.constructor "exFO"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun (m n : Nat)
                    (a :
                      Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  Lax58.StructuralCombinators.Raw.constructor "exSO"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (a a_2 :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{0, 1} Nat m
              (fun {m_2 : Nat} =>
                ∀
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 a a_2)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                    (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                      (fun (m n : Nat)
                          (value :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralPresentation.Raw)
                      m n value
                      (fun (m n : Nat) =>
                        Lax58.StructuralCombinators.Raw.constructor "falsum"
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                      (fun (m n : Nat)
                          (a a_3 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "equal"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a a_4 :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_4 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_3 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "rel"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                              ((fun (n m k : Nat)
                                    (a :
                                      FirstOrder.Language.Relations.{0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        k)
                                    (a_4 :
                                      Fin k →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                n m k a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                ((i : Fin k) →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (fun
                                    (f :
                                      (i : Fin k) →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  Lax58.StructuralCombinators.Raw.fields
                                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_4 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                      (fun (i : Fin k) =>
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                      fun (a : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m k a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_3 : Fin m) =>
                        Lax58.StructuralCombinators.Raw.constructor "mem"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n))
                                    (a_4 : Fin m) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (∀ (i : Fin m),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_4 : Fin m) =>
                                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                  n m a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a a_3 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "or"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "neg"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m) =>
                        Lax58.StructuralCombinators.Raw.constructor "exFO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      fun (m n : Nat)
                        (a :
                          Lax52.MSOSyntax.Formula.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      Lax58.StructuralCombinators.Raw.constructor "exSO"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)) =>
                @Eq.ndrec.{0, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a a_2)
                  (fun
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                        (fun (m n : Nat)
                            (value :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralPresentation.Raw)
                        m n value
                        (fun (m n : Nat) =>
                          Lax58.StructuralCombinators.Raw.constructor "falsum"
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                        (fun (m n : Nat)
                            (a a_3 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "equal"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_4 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  (FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m : Nat)
                                        (a a_4 :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_3 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "rel"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_4 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                  n m k a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  ((i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun
                                      (f :
                                        (i : Fin k) →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    Lax58.StructuralCombinators.Raw.fields
                                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m k : Nat)
                                        (a :
                                          FirstOrder.Language.Relations.{0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            k)
                                        (a_4 :
                                          Fin k →
                                            FirstOrder.Language.Term.{0, 0, 0}
                                              (Lax53.TreeStructure.treeSignature.{0}
                                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                              (Fin n)) =>
                                      @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                        (fun (i : Fin k) =>
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                        (fun (i : Fin k) =>
                                          @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                        fun (a : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m k a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_3 : Fin m) =>
                          Lax58.StructuralCombinators.Raw.constructor "mem"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_4 : Fin m) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                  (∀ (i : Fin m),
                                    @Eq.{1} Lax58.StructuralPresentation.Raw
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                  ((fun (n m : Nat)
                                        (a :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (a_4 : Fin m) =>
                                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                    n m a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a a_3 :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "or"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "neg"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m) =>
                          Lax58.StructuralCombinators.Raw.constructor "exFO"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        Lax58.StructuralCombinators.Raw.constructor "exSO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)))
                  value
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    value
                    (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a a_2)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (@Lax52.MSOSyntax.Formula.equal.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)
                      h)))
              m_1 h)
          n_1 h a a_1)
      (fun {n_1 m_1 k : Nat}
          (a :
            FirstOrder.Language.Relations.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              k)
          (a_1 :
            Fin k →
              FirstOrder.Language.Term.{0, 0, 0}
                (Lax53.TreeStructure.treeSignature.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (Fin n_1))
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{0, 1} Nat n
          (fun {n_2 : Nat} =>
            ∀
              (a_2 :
                Fin k →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n_2))
              (h : @Eq.{1} Nat m m_1)
              (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  value
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)
                  (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1 k a a_2)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                  (fun (m n : Nat)
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralPresentation.Raw)
                  m n value
                  (fun (m n : Nat) =>
                    Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                  (fun (m n : Nat)
                      (a a_3 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "equal"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a a_4 :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                            (@Lax53.StructuralRepresentations.termStructure alphabet n)
                            (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m : Nat)
                                  (a a_4 :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                                @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_3 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "rel"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                          (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                          (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                          ((fun (n m k : Nat)
                                (a :
                                  FirstOrder.Language.Relations.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    k)
                                (a_4 :
                                  Fin k →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                            n m k a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            ((i : Fin k) →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (fun
                                (f :
                                  (i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              Lax58.StructuralCombinators.Raw.fields
                                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                  @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                            (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m k : Nat)
                                  (a :
                                    FirstOrder.Language.Relations.{0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      k)
                                  (a_4 :
                                    Fin k →
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                  (fun (i : Fin k) =>
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m k a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_3 : Fin m) =>
                    Lax58.StructuralCombinators.Raw.constructor "mem"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (a_4 : Fin m) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                            (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (∀ (i : Fin m),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                            ((fun (n m : Nat)
                                  (a :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (a_4 : Fin m) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                              n m a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a a_3 :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "or"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "neg"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m) =>
                    Lax58.StructuralCombinators.Raw.constructor "exFO"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun (m n : Nat)
                    (a :
                      Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  Lax58.StructuralCombinators.Raw.constructor "exSO"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (a_2 :
                Fin k →
                  FirstOrder.Language.Term.{0, 0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (Fin n))
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{0, 1} Nat m
              (fun {m_2 : Nat} =>
                ∀
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 k a a_2)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                    (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                      (fun (m n : Nat)
                          (value :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralPresentation.Raw)
                      m n value
                      (fun (m n : Nat) =>
                        Lax58.StructuralCombinators.Raw.constructor "falsum"
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                      (fun (m n : Nat)
                          (a a_3 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "equal"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a a_4 :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_4 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_3 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "rel"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                              ((fun (n m k : Nat)
                                    (a :
                                      FirstOrder.Language.Relations.{0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        k)
                                    (a_4 :
                                      Fin k →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                n m k a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                ((i : Fin k) →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (fun
                                    (f :
                                      (i : Fin k) →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  Lax58.StructuralCombinators.Raw.fields
                                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_4 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                      (fun (i : Fin k) =>
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                      fun (a : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m k a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_3 : Fin m) =>
                        Lax58.StructuralCombinators.Raw.constructor "mem"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n))
                                    (a_4 : Fin m) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (∀ (i : Fin m),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_4 : Fin m) =>
                                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                  n m a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a a_3 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "or"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "neg"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m) =>
                        Lax58.StructuralCombinators.Raw.constructor "exFO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      fun (m n : Nat)
                        (a :
                          Lax52.MSOSyntax.Formula.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      Lax58.StructuralCombinators.Raw.constructor "exSO"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m k a a_2)) =>
                @Eq.ndrec.{0, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m k a a_2)
                  (fun
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                        (fun (m n : Nat)
                            (value :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralPresentation.Raw)
                        m n value
                        (fun (m n : Nat) =>
                          Lax58.StructuralCombinators.Raw.constructor "falsum"
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                        (fun (m n : Nat)
                            (a a_3 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "equal"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_4 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  (FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m : Nat)
                                        (a a_4 :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_3 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "rel"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_4 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                  n m k a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  ((i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun
                                      (f :
                                        (i : Fin k) →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    Lax58.StructuralCombinators.Raw.fields
                                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m k : Nat)
                                        (a :
                                          FirstOrder.Language.Relations.{0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            k)
                                        (a_4 :
                                          Fin k →
                                            FirstOrder.Language.Term.{0, 0, 0}
                                              (Lax53.TreeStructure.treeSignature.{0}
                                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                              (Fin n)) =>
                                      @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                        (fun (i : Fin k) =>
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                        (fun (i : Fin k) =>
                                          @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                        fun (a : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m k a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_3 : Fin m) =>
                          Lax58.StructuralCombinators.Raw.constructor "mem"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_4 : Fin m) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                  (∀ (i : Fin m),
                                    @Eq.{1} Lax58.StructuralPresentation.Raw
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                  ((fun (n m : Nat)
                                        (a :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (a_4 : Fin m) =>
                                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                    n m a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a a_3 :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "or"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "neg"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m) =>
                          Lax58.StructuralCombinators.Raw.constructor "exFO"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        Lax58.StructuralCombinators.Raw.constructor "exSO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m
                      (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m k a a_2)))
                  value
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    value
                    (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m k a a_2)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (@Lax52.MSOSyntax.Formula.rel.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m k a a_2)
                      h)))
              m_1 h)
          n_1 h a_1)
      (fun {n_1 m_1 : Nat}
          (a :
            FirstOrder.Language.Term.{0, 0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (Fin n_1))
          (a_1 : Fin m_1) (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{0, 1} Nat n
          (fun {n_2 : Nat} =>
            ∀
              (a :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n_2))
              (h : @Eq.{1} Nat m m_1)
              (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  value
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)
                  (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1 a a_1)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                  (fun (m n : Nat)
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralPresentation.Raw)
                  m n value
                  (fun (m n : Nat) =>
                    Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                  (fun (m n : Nat)
                      (a a_2 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "equal"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a a_3 :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_2)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                            (@Lax53.StructuralRepresentations.termStructure alphabet n)
                            (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m : Nat)
                                  (a a_3 :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                                @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m a a_2)
                            a_2)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_2 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "rel"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                          (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                          (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                          ((fun (n m k : Nat)
                                (a :
                                  FirstOrder.Language.Relations.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    k)
                                (a_3 :
                                  Fin k →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                            n m k a a_2)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            ((i : Fin k) →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (fun
                                (f :
                                  (i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              Lax58.StructuralCombinators.Raw.fields
                                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                  @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                            (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m k : Nat)
                                  (a :
                                    FirstOrder.Language.Relations.{0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      k)
                                  (a_3 :
                                    Fin k →
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                  (fun (i : Fin k) =>
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m k a a_2)
                            a_2)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_2 : Fin m) =>
                    Lax58.StructuralCombinators.Raw.constructor "mem"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (a_3 : Fin m) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_2)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                            (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (∀ (i : Fin m),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                            ((fun (n m : Nat)
                                  (a :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (a_3 : Fin m) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                              n m a a_2)
                            a_2)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a a_2 :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "or"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_2)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "neg"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m) =>
                    Lax58.StructuralCombinators.Raw.constructor "exFO"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun (m n : Nat)
                    (a :
                      Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  Lax58.StructuralCombinators.Raw.constructor "exSO"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (a :
                FirstOrder.Language.Term.{0, 0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (Fin n))
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{0, 1} Nat m
              (fun {m_2 : Nat} =>
                ∀ (a_2 : Fin m_2)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 a a_2)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                    (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                      (fun (m n : Nat)
                          (value :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralPresentation.Raw)
                      m n value
                      (fun (m n : Nat) =>
                        Lax58.StructuralCombinators.Raw.constructor "falsum"
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                      (fun (m n : Nat)
                          (a a_3 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "equal"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a a_4 :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_4 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_3 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "rel"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                              ((fun (n m k : Nat)
                                    (a :
                                      FirstOrder.Language.Relations.{0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        k)
                                    (a_4 :
                                      Fin k →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                n m k a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                ((i : Fin k) →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (fun
                                    (f :
                                      (i : Fin k) →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  Lax58.StructuralCombinators.Raw.fields
                                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_4 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                      (fun (i : Fin k) =>
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                      fun (a : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m k a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_3 : Fin m) =>
                        Lax58.StructuralCombinators.Raw.constructor "mem"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n))
                                    (a_4 : Fin m) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_3)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (∀ (i : Fin m),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_4 : Fin m) =>
                                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                  n m a a_3)
                                a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a a_3 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "or"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "neg"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m) =>
                        Lax58.StructuralCombinators.Raw.constructor "exFO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      fun (m n : Nat)
                        (a :
                          Lax52.MSOSyntax.Formula.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      Lax58.StructuralCombinators.Raw.constructor "exSO"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun (a_2 : Fin m)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)) =>
                @Eq.ndrec.{0, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a a_2)
                  (fun
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                        (fun (m n : Nat)
                            (value :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralPresentation.Raw)
                        m n value
                        (fun (m n : Nat) =>
                          Lax58.StructuralCombinators.Raw.constructor "falsum"
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                        (fun (m n : Nat)
                            (a a_3 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "equal"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_4 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  (FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m : Nat)
                                        (a a_4 :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_3 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "rel"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_4 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                  n m k a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  ((i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun
                                      (f :
                                        (i : Fin k) →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    Lax58.StructuralCombinators.Raw.fields
                                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m k : Nat)
                                        (a :
                                          FirstOrder.Language.Relations.{0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            k)
                                        (a_4 :
                                          Fin k →
                                            FirstOrder.Language.Term.{0, 0, 0}
                                              (Lax53.TreeStructure.treeSignature.{0}
                                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                              (Fin n)) =>
                                      @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                        (fun (i : Fin k) =>
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                        (fun (i : Fin k) =>
                                          @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                        fun (a : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m k a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_3 : Fin m) =>
                          Lax58.StructuralCombinators.Raw.constructor "mem"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_4 : Fin m) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_3)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                  (∀ (i : Fin m),
                                    @Eq.{1} Lax58.StructuralPresentation.Raw
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                  ((fun (n m : Nat)
                                        (a :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (a_4 : Fin m) =>
                                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                    n m a a_3)
                                  a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a a_3 :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "or"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "neg"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m) =>
                          Lax58.StructuralCombinators.Raw.constructor "exFO"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        Lax58.StructuralCombinators.Raw.constructor "exSO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m
                      (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)))
                  value
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    value
                    (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a a_2)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (@Lax52.MSOSyntax.Formula.mem.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_2)
                      h)))
              m_1 h a_1)
          n_1 h a)
      (fun {n_1 m_1 : Nat}
          (a a_1 :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n_1 m_1)
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{0, 1} Nat n
          (fun {n_2 : Nat} =>
            ∀
              (a a_2 :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n_2 m_1)
              (h : @Eq.{1} Nat m m_1)
              (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  value
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)
                  (@Lax52.MSOSyntax.Formula.or.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1 a a_2)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                  (fun (m n : Nat)
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralPresentation.Raw)
                  m n value
                  (fun (m n : Nat) =>
                    Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                  (fun (m n : Nat)
                      (a a_3 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "equal"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a a_4 :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                            (@Lax53.StructuralRepresentations.termStructure alphabet n)
                            (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m : Nat)
                                  (a a_4 :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                                @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_3 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "rel"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                          (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                          (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                          ((fun (n m k : Nat)
                                (a :
                                  FirstOrder.Language.Relations.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    k)
                                (a_4 :
                                  Fin k →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                            n m k a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            ((i : Fin k) →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (fun
                                (f :
                                  (i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              Lax58.StructuralCombinators.Raw.fields
                                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                  @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                            (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m k : Nat)
                                  (a :
                                    FirstOrder.Language.Relations.{0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      k)
                                  (a_4 :
                                    Fin k →
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                  (fun (i : Fin k) =>
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m k a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_3 : Fin m) =>
                    Lax58.StructuralCombinators.Raw.constructor "mem"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (a_4 : Fin m) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_3)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                            (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (∀ (i : Fin m),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                            ((fun (n m : Nat)
                                  (a :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (a_4 : Fin m) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                              n m a a_3)
                            a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a a_3 :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "or"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_3)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "neg"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m) =>
                    Lax58.StructuralCombinators.Raw.constructor "exFO"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun (m n : Nat)
                    (a :
                      Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  Lax58.StructuralCombinators.Raw.constructor "exSO"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (a a_2 :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m_1)
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{0, 1} Nat m
              (fun {m_2 : Nat} =>
                ∀
                  (a a_3 :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m_2)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.or.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 a a_3)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                    (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                      (fun (m n : Nat)
                          (value :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralPresentation.Raw)
                      m n value
                      (fun (m n : Nat) =>
                        Lax58.StructuralCombinators.Raw.constructor "falsum"
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                      (fun (m n : Nat)
                          (a a_4 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "equal"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a a_5 :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_4)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_5 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_4)
                                a_4)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_4 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "rel"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                              ((fun (n m k : Nat)
                                    (a :
                                      FirstOrder.Language.Relations.{0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        k)
                                    (a_5 :
                                      Fin k →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                n m k a a_4)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                ((i : Fin k) →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (fun
                                    (f :
                                      (i : Fin k) →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  Lax58.StructuralCombinators.Raw.fields
                                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_5 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                      (fun (i : Fin k) =>
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                      fun (a : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m k a a_4)
                                a_4)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_4 : Fin m) =>
                        Lax58.StructuralCombinators.Raw.constructor "mem"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n))
                                    (a_5 : Fin m) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_4)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (∀ (i : Fin m),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_5 : Fin m) =>
                                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                  n m a a_4)
                                a_4)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a a_4 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "or"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_4)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "neg"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m) =>
                        Lax58.StructuralCombinators.Raw.constructor "exFO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      fun (m n : Nat)
                        (a :
                          Lax52.MSOSyntax.Formula.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      Lax58.StructuralCombinators.Raw.constructor "exSO"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun
                  (a a_3 :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.or.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_3)) =>
                @Eq.ndrec.{0, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.or.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a a_3)
                  (fun
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                        (fun (m n : Nat)
                            (value :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralPresentation.Raw)
                        m n value
                        (fun (m n : Nat) =>
                          Lax58.StructuralCombinators.Raw.constructor "falsum"
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                        (fun (m n : Nat)
                            (a a_4 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "equal"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_5 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_4)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  (FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m : Nat)
                                        (a a_5 :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m a a_4)
                                  a_4)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_4 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "rel"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_5 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                  n m k a a_4)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  ((i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun
                                      (f :
                                        (i : Fin k) →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    Lax58.StructuralCombinators.Raw.fields
                                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m k : Nat)
                                        (a :
                                          FirstOrder.Language.Relations.{0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            k)
                                        (a_5 :
                                          Fin k →
                                            FirstOrder.Language.Term.{0, 0, 0}
                                              (Lax53.TreeStructure.treeSignature.{0}
                                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                              (Fin n)) =>
                                      @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                        (fun (i : Fin k) =>
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                        (fun (i : Fin k) =>
                                          @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                        fun (a : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m k a a_4)
                                  a_4)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_4 : Fin m) =>
                          Lax58.StructuralCombinators.Raw.constructor "mem"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_5 : Fin m) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_4)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                  (∀ (i : Fin m),
                                    @Eq.{1} Lax58.StructuralPresentation.Raw
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                  ((fun (n m : Nat)
                                        (a :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (a_5 : Fin m) =>
                                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                    n m a a_4)
                                  a_4)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a a_4 :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "or"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_4)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "neg"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m) =>
                          Lax58.StructuralCombinators.Raw.constructor "exFO"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        Lax58.StructuralCombinators.Raw.constructor "exSO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m
                      (@Lax52.MSOSyntax.Formula.or.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_3)))
                  value
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    value
                    (@Lax52.MSOSyntax.Formula.or.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a a_3)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (@Lax52.MSOSyntax.Formula.or.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a a_3)
                      h)))
              m_1 h a a_2)
          n_1 h a a_1)
      (fun {n_1 m_1 : Nat}
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n_1 m_1)
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{0, 1} Nat n
          (fun {n_2 : Nat} =>
            ∀
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n_2 m_1)
              (h : @Eq.{1} Nat m m_1)
              (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  value
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)
                  (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1 a)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                  (fun (m n : Nat)
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralPresentation.Raw)
                  m n value
                  (fun (m n : Nat) =>
                    Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                  (fun (m n : Nat)
                      (a a_1 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "equal"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a a_2 :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                            (@Lax53.StructuralRepresentations.termStructure alphabet n)
                            (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m : Nat)
                                  (a a_2 :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                                @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_1 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "rel"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                          (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                          (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                          ((fun (n m k : Nat)
                                (a :
                                  FirstOrder.Language.Relations.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    k)
                                (a_2 :
                                  Fin k →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                            n m k a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            ((i : Fin k) →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (fun
                                (f :
                                  (i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              Lax58.StructuralCombinators.Raw.fields
                                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                  @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                            (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m k : Nat)
                                  (a :
                                    FirstOrder.Language.Relations.{0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      k)
                                  (a_2 :
                                    Fin k →
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                  (fun (i : Fin k) =>
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m k a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_1 : Fin m) =>
                    Lax58.StructuralCombinators.Raw.constructor "mem"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (a_2 : Fin m) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                            (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (∀ (i : Fin m),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                            ((fun (n m : Nat)
                                  (a :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (a_2 : Fin m) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                              n m a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a a_1 :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "or"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "neg"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m) =>
                    Lax58.StructuralCombinators.Raw.constructor "exFO"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun (m n : Nat)
                    (a :
                      Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  Lax58.StructuralCombinators.Raw.constructor "exSO"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n m_1)
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{0, 1} Nat m
              (fun {m_2 : Nat} =>
                ∀
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m_2)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 a)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                    (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                      (fun (m n : Nat)
                          (value :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralPresentation.Raw)
                      m n value
                      (fun (m n : Nat) =>
                        Lax58.StructuralCombinators.Raw.constructor "falsum"
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                      (fun (m n : Nat)
                          (a a_1 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "equal"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a a_2 :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_2 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_1 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "rel"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                              ((fun (n m k : Nat)
                                    (a :
                                      FirstOrder.Language.Relations.{0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        k)
                                    (a_2 :
                                      Fin k →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                n m k a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                ((i : Fin k) →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (fun
                                    (f :
                                      (i : Fin k) →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  Lax58.StructuralCombinators.Raw.fields
                                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_2 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                      (fun (i : Fin k) =>
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                      fun (a : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m k a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_1 : Fin m) =>
                        Lax58.StructuralCombinators.Raw.constructor "mem"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n))
                                    (a_2 : Fin m) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (∀ (i : Fin m),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_2 : Fin m) =>
                                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                  n m a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a a_1 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "or"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "neg"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m) =>
                        Lax58.StructuralCombinators.Raw.constructor "exFO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      fun (m n : Nat)
                        (a :
                          Lax52.MSOSyntax.Formula.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      Lax58.StructuralCombinators.Raw.constructor "exSO"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)) =>
                @Eq.ndrec.{0, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a)
                  (fun
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                        (fun (m n : Nat)
                            (value :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralPresentation.Raw)
                        m n value
                        (fun (m n : Nat) =>
                          Lax58.StructuralCombinators.Raw.constructor "falsum"
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                        (fun (m n : Nat)
                            (a a_1 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "equal"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_2 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  (FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m : Nat)
                                        (a a_2 :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_1 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "rel"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_2 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                  n m k a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  ((i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun
                                      (f :
                                        (i : Fin k) →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    Lax58.StructuralCombinators.Raw.fields
                                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m k : Nat)
                                        (a :
                                          FirstOrder.Language.Relations.{0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            k)
                                        (a_2 :
                                          Fin k →
                                            FirstOrder.Language.Term.{0, 0, 0}
                                              (Lax53.TreeStructure.treeSignature.{0}
                                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                              (Fin n)) =>
                                      @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                        (fun (i : Fin k) =>
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                        (fun (i : Fin k) =>
                                          @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                        fun (a : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m k a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_1 : Fin m) =>
                          Lax58.StructuralCombinators.Raw.constructor "mem"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_2 : Fin m) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                  (∀ (i : Fin m),
                                    @Eq.{1} Lax58.StructuralPresentation.Raw
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                  ((fun (n m : Nat)
                                        (a :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (a_2 : Fin m) =>
                                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                    n m a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a a_1 :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "or"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "neg"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m) =>
                          Lax58.StructuralCombinators.Raw.constructor "exFO"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        Lax58.StructuralCombinators.Raw.constructor "exSO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m
                      (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)))
                  value
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    value
                    (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (@Lax52.MSOSyntax.Formula.neg.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)
                      h)))
              m_1 h a)
          n_1 h a)
      (fun {n_1 m_1 : Nat}
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_1
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              m_1)
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{0, 1} Nat n
          (fun {n_2 : Nat} =>
            ∀
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n_2
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  m_1)
              (h : @Eq.{1} Nat m m_1)
              (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  value
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)
                  (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1 a)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                  (fun (m n : Nat)
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralPresentation.Raw)
                  m n value
                  (fun (m n : Nat) =>
                    Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                  (fun (m n : Nat)
                      (a a_1 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "equal"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a a_2 :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                            (@Lax53.StructuralRepresentations.termStructure alphabet n)
                            (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m : Nat)
                                  (a a_2 :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                                @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_1 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "rel"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                          (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                          (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                          ((fun (n m k : Nat)
                                (a :
                                  FirstOrder.Language.Relations.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    k)
                                (a_2 :
                                  Fin k →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                            n m k a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            ((i : Fin k) →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (fun
                                (f :
                                  (i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              Lax58.StructuralCombinators.Raw.fields
                                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                  @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                            (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m k : Nat)
                                  (a :
                                    FirstOrder.Language.Relations.{0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      k)
                                  (a_2 :
                                    Fin k →
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                  (fun (i : Fin k) =>
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m k a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_1 : Fin m) =>
                    Lax58.StructuralCombinators.Raw.constructor "mem"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (a_2 : Fin m) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                            (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (∀ (i : Fin m),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                            ((fun (n m : Nat)
                                  (a :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (a_2 : Fin m) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                              n m a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a a_1 :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "or"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "neg"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m) =>
                    Lax58.StructuralCombinators.Raw.constructor "exFO"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun (m n : Nat)
                    (a :
                      Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  Lax58.StructuralCombinators.Raw.constructor "exSO"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  m_1)
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{0, 1} Nat m
              (fun {m_2 : Nat} =>
                ∀
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      m_2)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 a)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                    (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                      (fun (m n : Nat)
                          (value :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralPresentation.Raw)
                      m n value
                      (fun (m n : Nat) =>
                        Lax58.StructuralCombinators.Raw.constructor "falsum"
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                      (fun (m n : Nat)
                          (a a_1 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "equal"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a a_2 :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_2 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_1 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "rel"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                              ((fun (n m k : Nat)
                                    (a :
                                      FirstOrder.Language.Relations.{0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        k)
                                    (a_2 :
                                      Fin k →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                n m k a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                ((i : Fin k) →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (fun
                                    (f :
                                      (i : Fin k) →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  Lax58.StructuralCombinators.Raw.fields
                                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_2 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                      (fun (i : Fin k) =>
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                      fun (a : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m k a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_1 : Fin m) =>
                        Lax58.StructuralCombinators.Raw.constructor "mem"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n))
                                    (a_2 : Fin m) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (∀ (i : Fin m),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_2 : Fin m) =>
                                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                  n m a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a a_1 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "or"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "neg"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m) =>
                        Lax58.StructuralCombinators.Raw.constructor "exFO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      fun (m n : Nat)
                        (a :
                          Lax52.MSOSyntax.Formula.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      Lax58.StructuralCombinators.Raw.constructor "exSO"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      m)
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)) =>
                @Eq.ndrec.{0, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a)
                  (fun
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                        (fun (m n : Nat)
                            (value :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralPresentation.Raw)
                        m n value
                        (fun (m n : Nat) =>
                          Lax58.StructuralCombinators.Raw.constructor "falsum"
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                        (fun (m n : Nat)
                            (a a_1 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "equal"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_2 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  (FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m : Nat)
                                        (a a_2 :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_1 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "rel"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_2 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                  n m k a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  ((i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun
                                      (f :
                                        (i : Fin k) →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    Lax58.StructuralCombinators.Raw.fields
                                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m k : Nat)
                                        (a :
                                          FirstOrder.Language.Relations.{0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            k)
                                        (a_2 :
                                          Fin k →
                                            FirstOrder.Language.Term.{0, 0, 0}
                                              (Lax53.TreeStructure.treeSignature.{0}
                                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                              (Fin n)) =>
                                      @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                        (fun (i : Fin k) =>
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                        (fun (i : Fin k) =>
                                          @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                        fun (a : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m k a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_1 : Fin m) =>
                          Lax58.StructuralCombinators.Raw.constructor "mem"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_2 : Fin m) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                  (∀ (i : Fin m),
                                    @Eq.{1} Lax58.StructuralPresentation.Raw
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                  ((fun (n m : Nat)
                                        (a :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (a_2 : Fin m) =>
                                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                    n m a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a a_1 :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "or"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "neg"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m) =>
                          Lax58.StructuralCombinators.Raw.constructor "exFO"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        Lax58.StructuralCombinators.Raw.constructor "exSO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m
                      (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)))
                  value
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    value
                    (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (@Lax52.MSOSyntax.Formula.exFO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)
                      h)))
              m_1 h a)
          n_1 h a)
      (fun {n_1 m_1 : Nat}
          (a :
            Lax52.MSOSyntax.Formula.{0, 0}
              (Lax53.TreeStructure.treeSignature.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              n_1
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (h : @Eq.{1} Nat n n_1) =>
        @Eq.ndrec.{0, 1} Nat n
          (fun {n_2 : Nat} =>
            ∀
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n_2
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (h : @Eq.{1} Nat m m_1)
              (h :
                @HEq.{1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  value
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1)
                  (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n_2 m_1 a)),
              @Eq.{1} Lax58.StructuralPresentation.Raw
                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                  (fun (m n : Nat)
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralPresentation.Raw)
                  m n value
                  (fun (m n : Nat) =>
                    Lax58.StructuralCombinators.Raw.constructor "falsum" (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                  (fun (m n : Nat)
                      (a a_1 :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "equal"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a a_2 :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n)) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            (FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                            (@Lax53.StructuralRepresentations.termStructure alphabet n)
                            (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m : Nat)
                                  (a a_2 :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                                @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n k : Nat)
                      (a :
                        FirstOrder.Language.Relations.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          k)
                      (a_1 :
                        Fin k →
                          FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n)) =>
                    Lax58.StructuralCombinators.Raw.constructor "rel"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Relations.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            k)
                          (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                          (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                          ((fun (n m k : Nat)
                                (a :
                                  FirstOrder.Language.Relations.{0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    k)
                                (a_2 :
                                  Fin k →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                            n m k a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                            ((i : Fin k) →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (fun
                                (f :
                                  (i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n)) =>
                              Lax58.StructuralCombinators.Raw.fields
                                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                  @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                            (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                            ((fun (n m k : Nat)
                                  (a :
                                    FirstOrder.Language.Relations.{0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      k)
                                  (a_2 :
                                    Fin k →
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                  (fun (i : Fin k) =>
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  fun (a : Fin k) => @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                              n m k a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        FirstOrder.Language.Term.{0, 0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (Fin n))
                      (a_1 : Fin m) =>
                    Lax58.StructuralCombinators.Raw.constructor "mem"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                          (FirstOrder.Language.Term.{0, 0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (Fin n))
                          (@Lax53.StructuralRepresentations.termStructure alphabet n)
                          (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                          ((fun (n m : Nat)
                                (a :
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (a_2 : Fin m) =>
                              @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                            n m a a_1)
                          a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                            (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                            (∀ (i : Fin m),
                              @Eq.{1} Lax58.StructuralPresentation.Raw
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                            ((fun (n m : Nat)
                                  (a :
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (a_2 : Fin m) =>
                                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                              n m a a_1)
                            a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a a_1 :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "or"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    Lax58.StructuralCombinators.Raw.constructor "neg"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  (fun (m n : Nat)
                      (a :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m) =>
                    Lax58.StructuralCombinators.Raw.constructor "exFO"
                      (@List.cons.{0} Lax58.StructuralPresentation.Raw
                        (@Lax53.StructuralRepresentations.formulaStructure alphabet
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          m a)
                        (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                  fun (m n : Nat)
                    (a :
                      Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                  Lax58.StructuralCombinators.Raw.constructor "exSO"
                    (@List.cons.{0} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        a)
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
          (fun
              (a :
                Lax52.MSOSyntax.Formula.{0, 0}
                  (Lax53.TreeStructure.treeSignature.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  n
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (h : @Eq.{1} Nat m m_1) =>
            @Eq.ndrec.{0, 1} Nat m
              (fun {m_2 : Nat} =>
                ∀
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_2
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2)
                      (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m_2 a)),
                  @Eq.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                    (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                      (fun (m n : Nat)
                          (value :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralPresentation.Raw)
                      m n value
                      (fun (m n : Nat) =>
                        Lax58.StructuralCombinators.Raw.constructor "falsum"
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                      (fun (m n : Nat)
                          (a a_1 :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "equal"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a a_2 :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n)) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_2 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n k : Nat)
                          (a :
                            FirstOrder.Language.Relations.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              k)
                          (a_1 :
                            Fin k →
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                        Lax58.StructuralCombinators.Raw.constructor "rel"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                              (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                              (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                              ((fun (n m k : Nat)
                                    (a :
                                      FirstOrder.Language.Relations.{0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        k)
                                    (a_2 :
                                      Fin k →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                n m k a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                ((i : Fin k) →
                                  FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                (fun
                                    (f :
                                      (i : Fin k) →
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                  Lax58.StructuralCombinators.Raw.fields
                                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_2 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                      (fun (i : Fin k) =>
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                      (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                      fun (a : Fin k) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m k a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            FirstOrder.Language.Term.{0, 0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (Fin n))
                          (a_1 : Fin m) =>
                        Lax58.StructuralCombinators.Raw.constructor "mem"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                              (FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                              (@Lax53.StructuralRepresentations.termStructure alphabet n)
                              (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                              ((fun (n m : Nat)
                                    (a :
                                      FirstOrder.Language.Term.{0, 0, 0}
                                        (Lax53.TreeStructure.treeSignature.{0}
                                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                        (Fin n))
                                    (a_2 : Fin m) =>
                                  @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                n m a a_1)
                              a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                (∀ (i : Fin m),
                                  @Eq.{1} Lax58.StructuralPresentation.Raw
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                    (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_2 : Fin m) =>
                                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                  n m a a_1)
                                a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a a_1 :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "or"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n m) =>
                        Lax58.StructuralCombinators.Raw.constructor "neg"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      (fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m) =>
                        Lax58.StructuralCombinators.Raw.constructor "exFO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              m a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                      fun (m n : Nat)
                        (a :
                          Lax52.MSOSyntax.Formula.{0, 0}
                            (Lax53.TreeStructure.treeSignature.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                      Lax58.StructuralCombinators.Raw.constructor "exSO"
                        (@List.cons.{0} Lax58.StructuralPresentation.Raw
                          (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            a)
                          (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
              (fun
                  (a :
                    Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (h :
                    @HEq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)) =>
                @Eq.ndrec.{0, 1}
                  (Lax52.MSOSyntax.Formula.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m)
                  (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                    (Lax53.TreeStructure.treeSignature.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    n m a)
                  (fun
                      (value :
                        Lax52.MSOSyntax.Formula.{0, 0}
                          (Lax53.TreeStructure.treeSignature.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          n m) =>
                    @Eq.{1} Lax58.StructuralPresentation.Raw
                      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m value)
                      (Lax53.StructuralRepresentations.formulaStructure.match_1.{1} alphabet
                        (fun (m n : Nat)
                            (value :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralPresentation.Raw)
                        m n value
                        (fun (m n : Nat) =>
                          Lax58.StructuralCombinators.Raw.constructor "falsum"
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))
                        (fun (m n : Nat)
                            (a a_1 :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "equal"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a a_2 :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n)) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  (FirstOrder.Language.Term.{0, 0, 0}
                                    (Lax53.TreeStructure.treeSignature.{0}
                                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                    (Fin n))
                                  (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                  (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m : Nat)
                                        (a a_2 :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                      @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n k : Nat)
                            (a :
                              FirstOrder.Language.Relations.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                k)
                            (a_1 :
                              Fin k →
                                FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n)) =>
                          Lax58.StructuralCombinators.Raw.constructor "rel"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Relations.{0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  k)
                                (@Lax53.StructuralRepresentations.relationStructure alphabet k)
                                (@Lax53.StructuralRepresentations.relationStructure.Laws alphabet k)
                                ((fun (n m k : Nat)
                                      (a :
                                        FirstOrder.Language.Relations.{0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          k)
                                      (a_2 :
                                        Fin k →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    @Lax53.StructuralRepresentations.relationStructure.certified alphabet k)
                                  n m k a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                  ((i : Fin k) →
                                    FirstOrder.Language.Term.{0, 0, 0}
                                      (Lax53.TreeStructure.treeSignature.{0}
                                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                      (Fin n))
                                  (fun
                                      (f :
                                        (i : Fin k) →
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n)) =>
                                    Lax58.StructuralCombinators.Raw.fields
                                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw k fun (i : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure alphabet n (f i)))
                                  (∀ (i : Fin k), @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                  ((fun (n m k : Nat)
                                        (a :
                                          FirstOrder.Language.Relations.{0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            k)
                                        (a_2 :
                                          Fin k →
                                            FirstOrder.Language.Term.{0, 0, 0}
                                              (Lax53.TreeStructure.treeSignature.{0}
                                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                              (Fin n)) =>
                                      @Lax58.CertifiedDerivation.CertifiedFieldEncoding.family.{0} k
                                        (fun (i : Fin k) =>
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (fun (i : Fin k) => @Lax53.StructuralRepresentations.termStructure alphabet n)
                                        (fun (i : Fin k) =>
                                          @Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                        fun (a : Fin k) =>
                                        @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                    n m k a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              FirstOrder.Language.Term.{0, 0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (Fin n))
                            (a_1 : Fin m) =>
                          Lax58.StructuralCombinators.Raw.constructor "mem"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0}
                                (FirstOrder.Language.Term.{0, 0, 0}
                                  (Lax53.TreeStructure.treeSignature.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                  (Fin n))
                                (@Lax53.StructuralRepresentations.termStructure alphabet n)
                                (@Lax53.StructuralRepresentations.termStructure.Laws alphabet n)
                                ((fun (n m : Nat)
                                      (a :
                                        FirstOrder.Language.Term.{0, 0, 0}
                                          (Lax53.TreeStructure.treeSignature.{0}
                                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                          (Fin n))
                                      (a_2 : Fin m) =>
                                    @Lax53.StructuralRepresentations.termStructure.certified alphabet n)
                                  n m a a_1)
                                a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin m)
                                  (fun (i : Fin m) => Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                  (∀ (i : Fin m),
                                    @Eq.{1} Lax58.StructuralPresentation.Raw
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i))
                                      (Lax58.StructuralPresentation.Raw.nat (@Fin.val m i)))
                                  ((fun (n m : Nat)
                                        (a :
                                          FirstOrder.Language.Term.{0, 0, 0}
                                            (Lax53.TreeStructure.treeSignature.{0}
                                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                            (Fin n))
                                        (a_2 : Fin m) =>
                                      Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin m)
                                    n m a a_1)
                                  a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a a_1 :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "or"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.cons.{0} Lax58.StructuralPresentation.Raw
                                (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a_1)
                                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                n m) =>
                          Lax58.StructuralCombinators.Raw.constructor "neg"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet n m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        (fun (m n : Nat)
                            (a :
                              Lax52.MSOSyntax.Formula.{0, 0}
                                (Lax53.TreeStructure.treeSignature.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m) =>
                          Lax58.StructuralCombinators.Raw.constructor "exFO"
                            (@List.cons.{0} Lax58.StructuralPresentation.Raw
                              (@Lax53.StructuralRepresentations.formulaStructure alphabet
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                m a)
                              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))
                        fun (m n : Nat)
                          (a :
                            Lax52.MSOSyntax.Formula.{0, 0}
                              (Lax53.TreeStructure.treeSignature.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                              n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                        Lax58.StructuralCombinators.Raw.constructor "exSO"
                          (@List.cons.{0} Lax58.StructuralPresentation.Raw
                            (@Lax53.StructuralRepresentations.formulaStructure alphabet n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              a)
                            (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
                  (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
                    (@Lax53.StructuralRepresentations.formulaStructure alphabet n m
                      (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)))
                  value
                  (@Eq.symm.{1}
                    (Lax52.MSOSyntax.Formula.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m)
                    value
                    (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                      (Lax53.TreeStructure.treeSignature.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      n m a)
                    (@eq_of_heq.{1}
                      (Lax52.MSOSyntax.Formula.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m)
                      value
                      (@Lax52.MSOSyntax.Formula.exSO.{0, 0}
                        (Lax53.TreeStructure.treeSignature.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                        n m a)
                      h)))
              m_1 h a)
          n_1 h a)
      (@Eq.refl.{1} Nat n) (@Eq.refl.{1} Nat m)
      (@HEq.refl.{1}
        (Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m)
        value)

noncomputable def _root_.Lax53.StructuralRepresentations.formulaStructure.certified :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    {n m : Nat} →
      Lax58.CertifiedDerivation.CertifiedFieldEncoding.{0}
        (Lax52.MSOSyntax.Formula.{0, 0}
          (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
          m)
        (@Lax53.StructuralRepresentations.formulaStructure alphabet n m)
        (@Lax53.StructuralRepresentations.formulaStructure.Laws alphabet n m) :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) {n m : Nat} =>
    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.ofLaws.{0}
      (Lax52.MSOSyntax.Formula.{0, 0}
        (Lax53.TreeStructure.treeSignature.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) n
        m)
      (@Lax53.StructuralRepresentations.formulaStructure alphabet n m)
      (@Lax53.StructuralRepresentations.formulaStructure.Laws alphabet n m)
      (@Lax53.StructuralRepresentations.formulaStructure.certified._proof_1 alphabet n m)

end Lax53.StructuralRepresentations
end

-- Lax53.TreeModelCheckingEncoding
noncomputable section
namespace Lax53.TreeModelCheckingEncoding.AutomatonAcceptanceInstance
end Lax53.TreeModelCheckingEncoding.AutomatonAcceptanceInstance

namespace Lax53.TreeModelCheckingEncoding

open Lax53.RankedTree

open Lax53.ValueTranslations

open Lax53.StructuralRepresentations

open Lax58.StructuralPresentation

open Lax58.StructuralPresentation.Presentation

open Lax58.StructuralCombinators

open Lax58.WordArena

/-- Number of constructor occurrences in a ranked tree. -/
def treeSize {A : RankedAlphabet} : Tree A → Nat
  | .node _ children =>
      1 + (List.ofFn fun i => treeSize (children i)).sum

/-- Largest symbol rank in a finite encoded alphabet. This is mathematical
alphabet data, independently of any evaluator representation. -/
def maximumRank (alphabet : RankedAlphabetCode) : Nat :=
  alphabet.foldl max 0

end Lax53.TreeModelCheckingEncoding
end

-- Lax13.Ram
noncomputable section
namespace Lax13
end Lax13

namespace Lax13.Ram
end Lax13.Ram

namespace Lax13.Ram.Instr
end Lax13.Ram.Instr

namespace Lax13.Ram.State
end Lax13.Ram.State

namespace Lax13.Ram.run
end Lax13.Ram.run

namespace Lax13.Ram.Instr.add
end Lax13.Ram.Instr.add

namespace Lax13.Ram.Instr.and
end Lax13.Ram.Instr.and

namespace Lax13.Ram.Instr.div
end Lax13.Ram.Instr.div

namespace Lax13.Ram.Instr.effect
end Lax13.Ram.Instr.effect

namespace Lax13.Ram.Instr.halt
end Lax13.Ram.Instr.halt

namespace Lax13.Ram.Instr.jump
end Lax13.Ram.Instr.jump

namespace Lax13.Ram.Instr.jzero
end Lax13.Ram.Instr.jzero

namespace Lax13.Ram.Instr.load
end Lax13.Ram.Instr.load

namespace Lax13.Ram.Instr.mul
end Lax13.Ram.Instr.mul

namespace Lax13.Ram.Instr.not
end Lax13.Ram.Instr.not

namespace Lax13.Ram.Instr.read
end Lax13.Ram.Instr.read

namespace Lax13.Ram.Instr.set
end Lax13.Ram.Instr.set

namespace Lax13.Ram.Instr.shiftl
end Lax13.Ram.Instr.shiftl

namespace Lax13.Ram.Instr.store
end Lax13.Ram.Instr.store

namespace Lax13.Ram.Instr.sub
end Lax13.Ram.Instr.sub

namespace Lax13.Ram.Instr.write
end Lax13.Ram.Instr.write
end

-- Lax13.RamComputes
noncomputable section
namespace Lax13.RamComputes
end Lax13.RamComputes
end

-- Lax58.RamComplexity
noncomputable section
namespace Lax58.RamComplexity
end Lax58.RamComplexity
end

-- Lax53.MSOLinearTime
noncomputable section
namespace Lax53.MSOLinearTime.ModelCheckingInstance
end Lax53.MSOLinearTime.ModelCheckingInstance

namespace Lax53.MSOLinearTime

open Lax52.MSOSyntax

open Lax53.RankedTree

open Lax53.TreeStructure

open Lax53.ValueTranslations

open Lax53.StructuralRepresentations

open Lax53.TreeModelCheckingEncoding

open Lax58.StructuralPresentation

open Lax58.StructuralPresentation.Presentation

open Lax58.StructuralCombinators

open Lax58.WordArena

open Lax58.RamComplexity

/-- Constructor size of an intrinsic MSO sentence, including its term and
relation fields but excluding any physical arena layout. -/
def sentenceSize (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) : Nat :=
  (formulaStructure alphabet phi).nodes

/-- Mathematical parameter size controlling the formula-dependent part of
the uniform algorithm. Symbol arity is explicit because one natural payload
can prescribe an arbitrarily large finite family. -/
def parameterSize (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) : Nat :=
  (derivedPresentation : Presentation RankedAlphabetCode).structuralSize alphabet +
    sentenceSize alphabet phi + maximumRank alphabet

/-- The actual instruction allowance for the uniform model checker. The
computable coefficient absorbs sentence compilation and the automaton
workload; the remaining dependence is linear in tree nodes. -/
def uniformTimeBound (coefficient : Nat → Nat)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  coefficient (parameterSize alphabet phi) * (treeSize t + 1)

end Lax53.MSOLinearTime
end
