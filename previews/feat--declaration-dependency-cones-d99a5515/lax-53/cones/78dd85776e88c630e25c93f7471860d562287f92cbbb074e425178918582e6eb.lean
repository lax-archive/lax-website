-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.ModelTheory.Semantics

-- Lax52.MSOSyntax
noncomputable section
namespace Lax52
end Lax52

namespace Lax52.MSOSyntax
end Lax52.MSOSyntax

namespace Lax52.MSOSyntax.Formula
end Lax52.MSOSyntax.Formula

namespace Lax52.MSOSyntax.Formula.equal
end Lax52.MSOSyntax.Formula.equal

namespace Lax52.MSOSyntax.Formula.exFO
end Lax52.MSOSyntax.Formula.exFO

namespace Lax52.MSOSyntax.Formula.exSO
end Lax52.MSOSyntax.Formula.exSO

namespace Lax52.MSOSyntax.Formula.falsum
end Lax52.MSOSyntax.Formula.falsum

namespace Lax52.MSOSyntax.Formula.mem
end Lax52.MSOSyntax.Formula.mem

namespace Lax52.MSOSyntax.Formula.neg
end Lax52.MSOSyntax.Formula.neg

namespace Lax52.MSOSyntax.Formula.or
end Lax52.MSOSyntax.Formula.or

namespace Lax52.MSOSyntax.Formula.rel
end Lax52.MSOSyntax.Formula.rel
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
namespace Lax53.TreeStructure
end Lax53.TreeStructure

namespace Lax53.TreeStructure.TreeRelation
end Lax53.TreeStructure.TreeRelation

namespace Lax53.TreeStructure.treeStructure
end Lax53.TreeStructure.treeStructure

namespace Lax53.TreeStructure.TreeRelation.child
end Lax53.TreeStructure.TreeRelation.child

namespace Lax53.TreeStructure.TreeRelation.label
end Lax53.TreeStructure.TreeRelation.label
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

/-- A finite transition consists of a symbol number, a parent-state number,
and the ordered list of child-state numbers. -/
abbrev TransitionCode := Nat × Nat × List Nat

/-- An automaton body consists of its number of states, transition list, and
accepting-state list. Its ranked alphabet is supplied separately. -/
abbrev AutomatonCode := Nat × List TransitionCode × List Nat

/-- A represented automaton packages its ranked alphabet with its body. -/
abbrev EncodedAutomaton := RankedAlphabetCode × AutomatonCode

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

/-- Largest natural-number payload occurring in a representation. -/
def maxNat : Raw → Nat
  | .nat n => n
  | .pair a b => max a.maxNat b.maxNat

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

namespace Presentation

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

instance {α β : Type} [A : Derivable α] [B : Derivable β] :
    Derivable (α × β) where
  presentation := prod A.presentation B.presentation
  generated := .prod A.generated B.generated

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
namespace Lax53.StructuralRepresentations.formulaStructure
end Lax53.StructuralRepresentations.formulaStructure

namespace Lax53.StructuralRepresentations.relationStructure
end Lax53.StructuralRepresentations.relationStructure

namespace Lax53.StructuralRepresentations.termStructure
end Lax53.StructuralRepresentations.termStructure

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

/-- Structural presentation of the complete finite automaton value. Its
components are derived automatically from the `Nat`, product, and ordered-list
structure of `EncodedAutomaton`. -/
def automatonPresentation : Presentation EncodedAutomaton :=
  derivedPresentation

-- Expanded from Lax58.CertifiedDerivationElab.deriveCertifiedEncoding
noncomputable def _root_.Lax53.StructuralRepresentations.treeStructure.match_1.{u_1} :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    (motive :
        Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) → Sort u_1) →
      (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
        (h_1 :
            (a :
                Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
              (children :
                  Fin
                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                    Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
                motive
                  (@Lax53.RankedTree.Tree.node.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
                    a children)) →
          motive x :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode)
      (motive :
        Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) → Sort u_1)
      (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (h_1 :
        (a :
            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
          (children :
              Fin
                  (Lax53.RankedTree.RankedAlphabet.rank.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
            motive
              (@Lax53.RankedTree.Tree.node.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a
                children)) =>
    @Lax53.RankedTree.Tree.casesOn.{u_1, 0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
      (fun (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
        motive x)
      x
      fun
        (a :
          Lax53.RankedTree.RankedAlphabet.Symbol.{0}
            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
        (children :
          Fin
              (Lax53.RankedTree.RankedAlphabet.rank.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
            Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
      h_1 a children

noncomputable def _root_.Lax53.StructuralRepresentations.treeStructure._f :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) →
      (f :
          @Lax53.RankedTree.Tree.below.{1, 0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
            (fun (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
              Lax58.StructuralPresentation.Raw)
            x) →
        Lax58.StructuralPresentation.Raw :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode)
      (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (f :
        @Lax53.RankedTree.Tree.below.{1, 0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
          (fun (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
            Lax58.StructuralPresentation.Raw)
          x) =>
    Lax53.StructuralRepresentations.treeStructure.match_1.{1} alphabet
      (fun (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
        @Lax53.RankedTree.Tree.below.{1, 0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
            (fun (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
              Lax58.StructuralPresentation.Raw)
            x →
          Lax58.StructuralPresentation.Raw)
      x
      (fun
          (a :
            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (children :
            Fin
                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
              Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (x :
            @Lax53.RankedTree.Tree.below.{1, 0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
              (fun
                  (x :
                    Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                Lax58.StructuralPresentation.Raw)
              (@Lax53.RankedTree.Tree.node.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a
                children)) =>
        Lax58.StructuralCombinators.Raw.constructor "node"
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
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                    (children :
                      Fin
                          (Lax53.RankedTree.RankedAlphabet.rank.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                        Lax53.RankedTree.Tree.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                  Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                a children)
              a)
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Lax58.StructuralPresentation.Raw)
              (List.{0} Lax58.StructuralPresentation.Raw) (List.{0} Lax58.StructuralPresentation.Raw)
              (@instHAppendOfAppend.{0} (List.{0} Lax58.StructuralPresentation.Raw)
                (@List.instAppend.{0} Lax58.StructuralPresentation.Raw))
              (@List.ofFn.{0} Lax58.StructuralPresentation.Raw
                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                fun
                  (i :
                    Fin
                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                (x i).1)
              (@List.nil.{0} Lax58.StructuralPresentation.Raw))))
      f

noncomputable def _root_.Lax53.StructuralRepresentations.treeStructure :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) →
      Lax58.StructuralPresentation.Raw :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode)
      (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
    @Lax53.RankedTree.Tree.brecOn.{1, 0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
      (fun (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
        Lax58.StructuralPresentation.Raw)
      x (Lax53.StructuralRepresentations.treeStructure._f alphabet)

noncomputable def _root_.Lax53.StructuralRepresentations.treeStructure.Laws :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) → Prop :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) =>
    ∀ (value : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)),
      @Eq.{1} Lax58.StructuralPresentation.Raw (Lax53.StructuralRepresentations.treeStructure alphabet value)
        (Lax53.StructuralRepresentations.treeStructure.match_1.{1} alphabet
          (fun
              (value :
                Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
            Lax58.StructuralPresentation.Raw)
          value
          fun
            (a :
              Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            (children :
              Fin
                  (Lax53.RankedTree.RankedAlphabet.rank.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
          Lax58.StructuralCombinators.Raw.constructor "node"
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
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                      (children :
                        Fin
                            (Lax53.RankedTree.RankedAlphabet.rank.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                          Lax53.RankedTree.Tree.{0}
                            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                  a children)
                a)
              (@HAppend.hAppend.{0, 0, 0} (List.{0} Lax58.StructuralPresentation.Raw)
                (List.{0} Lax58.StructuralPresentation.Raw) (List.{0} Lax58.StructuralPresentation.Raw)
                (@instHAppendOfAppend.{0} (List.{0} Lax58.StructuralPresentation.Raw)
                  (@List.instAppend.{0} Lax58.StructuralPresentation.Raw))
                (@List.ofFn.{0} Lax58.StructuralPresentation.Raw
                  (Lax53.RankedTree.RankedAlphabet.rank.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                  fun
                    (i :
                      Fin
                        (Lax53.RankedTree.RankedAlphabet.rank.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                  Lax53.StructuralRepresentations.treeStructure alphabet (children i))
                (@List.nil.{0} Lax58.StructuralPresentation.Raw))))

noncomputable def _root_.Lax53.StructuralRepresentations.treeStructure._sunfold :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) →
      Lax58.StructuralPresentation.Raw :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode)
      (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
    Lax53.StructuralRepresentations.treeStructure.match_1.{1} alphabet
      (fun (x : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
        Lax58.StructuralPresentation.Raw)
      x
      fun
        (a :
          Lax53.RankedTree.RankedAlphabet.Symbol.{0}
            (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
        (children :
          Fin
              (Lax53.RankedTree.RankedAlphabet.rank.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
            Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
      Lax58.StructuralCombinators.Raw.constructor "node"
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
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (children :
                    Fin
                        (Lax53.RankedTree.RankedAlphabet.rank.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                      Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
              a children)
            a)
          (@HAppend.hAppend.{0, 0, 0} (List.{0} Lax58.StructuralPresentation.Raw)
            (List.{0} Lax58.StructuralPresentation.Raw) (List.{0} Lax58.StructuralPresentation.Raw)
            (@instHAppendOfAppend.{0} (List.{0} Lax58.StructuralPresentation.Raw)
              (@List.instAppend.{0} Lax58.StructuralPresentation.Raw))
            (@List.ofFn.{0} Lax58.StructuralPresentation.Raw
              (Lax53.RankedTree.RankedAlphabet.rank.{0}
                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
              fun
                (i :
                  Fin
                    (Lax53.RankedTree.RankedAlphabet.rank.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
              Lax53.StructuralRepresentations.treeStructure alphabet (children i))
            (@List.nil.{0} Lax58.StructuralPresentation.Raw)))

theorem _root_.Lax53.StructuralRepresentations.treeStructure.certified._proof_1 :
  ∀ (alphabet : Lax53.ValueTranslations.RankedAlphabetCode)
    (value : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)),
    @Eq.{1} Lax58.StructuralPresentation.Raw (Lax53.StructuralRepresentations.treeStructure alphabet value)
      (Lax53.StructuralRepresentations.treeStructure.match_1.{1} alphabet
        (fun (value : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
          Lax58.StructuralPresentation.Raw)
        value
        fun
          (a :
            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (children :
            Fin
                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
              Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
        Lax58.StructuralCombinators.Raw.constructor "node"
          (@List.cons.{0} Lax58.StructuralPresentation.Raw
            (@Lax58.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} (Fin (@List.length.{0} Nat alphabet))
              (fun (i : Fin (@List.length.{0} Nat alphabet)) =>
                Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
              (∀ (i : Fin (@List.length.{0} Nat alphabet)),
                @Eq.{1} Lax58.StructuralPresentation.Raw
                  (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i))
                  (Lax58.StructuralPresentation.Raw.nat (@Fin.val (@List.length.{0} Nat alphabet) i)))
              (Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet)) a)
            (@HAppend.hAppend.{0, 0, 0} (List.{0} Lax58.StructuralPresentation.Raw)
              (List.{0} Lax58.StructuralPresentation.Raw) (List.{0} Lax58.StructuralPresentation.Raw)
              (@instHAppendOfAppend.{0} (List.{0} Lax58.StructuralPresentation.Raw)
                (@List.instAppend.{0} Lax58.StructuralPresentation.Raw))
              (@List.ofFn.{0} Lax58.StructuralPresentation.Raw
                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                fun
                  (i :
                    Fin
                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                Lax53.StructuralRepresentations.treeStructure alphabet (children i))
              (@List.nil.{0} Lax58.StructuralPresentation.Raw)))) :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode)
      (value : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
    @Lax53.RankedTree.Tree.casesOn.{0, 0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)
      (fun (t : Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
        ∀
          (h :
            @Eq.{1} (Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              value t),
          @Eq.{1} Lax58.StructuralPresentation.Raw (Lax53.StructuralRepresentations.treeStructure alphabet value)
            (Lax53.StructuralRepresentations.treeStructure.match_1.{1} alphabet
              (fun
                  (value :
                    Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                Lax58.StructuralPresentation.Raw)
              value
              fun
                (a :
                  Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                (children :
                  Fin
                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                    Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
              Lax58.StructuralCombinators.Raw.constructor "node"
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
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                          (children :
                            Fin
                                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                              Lax53.RankedTree.Tree.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                        Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                      a children)
                    a)
                  (@HAppend.hAppend.{0, 0, 0} (List.{0} Lax58.StructuralPresentation.Raw)
                    (List.{0} Lax58.StructuralPresentation.Raw) (List.{0} Lax58.StructuralPresentation.Raw)
                    (@instHAppendOfAppend.{0} (List.{0} Lax58.StructuralPresentation.Raw)
                      (@List.instAppend.{0} Lax58.StructuralPresentation.Raw))
                    (@List.ofFn.{0} Lax58.StructuralPresentation.Raw
                      (Lax53.RankedTree.RankedAlphabet.rank.{0}
                        (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                      fun
                        (i :
                          Fin
                            (Lax53.RankedTree.RankedAlphabet.rank.{0}
                              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                      Lax53.StructuralRepresentations.treeStructure alphabet (children i))
                    (@List.nil.{0} Lax58.StructuralPresentation.Raw)))))
      value
      (fun
          (a :
            Lax53.RankedTree.RankedAlphabet.Symbol.{0}
              (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (children :
            Fin
                (Lax53.RankedTree.RankedAlphabet.rank.{0}
                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
              Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (h :
            @Eq.{1} (Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
              value
              (@Lax53.RankedTree.Tree.node.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a
                children)) =>
        @Eq.ndrec.{0, 1}
          (Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
          (@Lax53.RankedTree.Tree.node.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a
            children)
          (fun
              (value :
                Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
            @Eq.{1} Lax58.StructuralPresentation.Raw (Lax53.StructuralRepresentations.treeStructure alphabet value)
              (Lax53.StructuralRepresentations.treeStructure.match_1.{1} alphabet
                (fun
                    (value :
                      Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                  Lax58.StructuralPresentation.Raw)
                value
                fun
                  (a :
                    Lax53.RankedTree.RankedAlphabet.Symbol.{0}
                      (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                  (children :
                    Fin
                        (Lax53.RankedTree.RankedAlphabet.rank.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                      Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                Lax58.StructuralCombinators.Raw.constructor "node"
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
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
                            (children :
                              Fin
                                  (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                    (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a) →
                                Lax53.RankedTree.Tree.{0}
                                  (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet)) =>
                          Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin (@List.length.{0} Nat alphabet))
                        a children)
                      a)
                    (@HAppend.hAppend.{0, 0, 0} (List.{0} Lax58.StructuralPresentation.Raw)
                      (List.{0} Lax58.StructuralPresentation.Raw) (List.{0} Lax58.StructuralPresentation.Raw)
                      (@instHAppendOfAppend.{0} (List.{0} Lax58.StructuralPresentation.Raw)
                        (@List.instAppend.{0} Lax58.StructuralPresentation.Raw))
                      (@List.ofFn.{0} Lax58.StructuralPresentation.Raw
                        (Lax53.RankedTree.RankedAlphabet.rank.{0}
                          (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)
                        fun
                          (i :
                            Fin
                              (Lax53.RankedTree.RankedAlphabet.rank.{0}
                                (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a)) =>
                        Lax53.StructuralRepresentations.treeStructure alphabet (children i))
                      (@List.nil.{0} Lax58.StructuralPresentation.Raw)))))
          (@Eq.refl.{1} Lax58.StructuralPresentation.Raw
            (Lax53.StructuralRepresentations.treeStructure alphabet
              (@Lax53.RankedTree.Tree.node.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a
                children)))
          value
          (@Eq.symm.{1} (Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
            value
            (@Lax53.RankedTree.Tree.node.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet) a
              children)
            h))
      (@Eq.refl.{1} (Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
        value)

noncomputable def _root_.Lax53.StructuralRepresentations.treeStructure.certified :
  (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) →
    Lax58.CertifiedDerivation.CertifiedFieldEncoding.{0}
      (Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (Lax53.StructuralRepresentations.treeStructure alphabet)
      (Lax53.StructuralRepresentations.treeStructure.Laws alphabet) :=
  fun (alphabet : Lax53.ValueTranslations.RankedAlphabetCode) =>
    @Lax58.CertifiedDerivation.CertifiedFieldEncoding.ofLaws.{0}
      (Lax53.RankedTree.Tree.{0} (Lax53.ValueTranslations.RankedAlphabetCode.toRankedAlphabet alphabet))
      (Lax53.StructuralRepresentations.treeStructure alphabet)
      (Lax53.StructuralRepresentations.treeStructure.Laws alphabet)
      (Lax53.StructuralRepresentations.treeStructure.certified._proof_1 alphabet)

end Lax53.StructuralRepresentations
end

-- Lax53.TreeModelCheckingEncoding
noncomputable section
namespace Lax53.TreeModelCheckingEncoding.AutomatonAcceptanceInstance
end Lax53.TreeModelCheckingEncoding.AutomatonAcceptanceInstance

namespace Lax53.TreeModelCheckingEncoding.treeSize
end Lax53.TreeModelCheckingEncoding.treeSize

namespace Lax53.TreeModelCheckingEncoding

open Lax53.RankedTree

open Lax53.ValueTranslations

open Lax53.StructuralRepresentations

open Lax58.StructuralPresentation

open Lax58.StructuralPresentation.Presentation

open Lax58.StructuralCombinators

open Lax58.WordArena

/-- Complete advice-free structural content of an automaton-evaluation
instance. Both fields use named, constructor-certified presentations. -/
def automatonTreeRaw (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Raw :=
  Raw.constructor "automatonAcceptance"
    [StructuralRepresentations.automatonPresentation.toRaw M,
      StructuralRepresentations.treeStructure M.1 t]

/-- Largest primitive natural payload in the complete structural input. -/
def inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Nat :=
  (automatonTreeRaw M t).maxNat

end Lax53.TreeModelCheckingEncoding
end
