-- Lax dependency cone
-- Lean: v4.33.0
-- Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

import Mathlib.Data.Nat.Pairing

-- Lax560851.StructuralPresentation
noncomputable section
namespace Lax560851.StructuralPresentation.Raw.nodes
end Lax560851.StructuralPresentation.Raw.nodes

namespace Lax560851.StructuralPresentation

universe u

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

end Raw

namespace Presentation

end Presentation

end Lax560851.StructuralPresentation
end

-- Lax560851.StructuralCombinators
noncomputable section
namespace Lax560851.StructuralCombinators.Derivable
end Lax560851.StructuralCombinators.Derivable

namespace Lax560851.StructuralCombinators.Generated
end Lax560851.StructuralCombinators.Generated

namespace Lax560851.StructuralCombinators.Lawful
end Lax560851.StructuralCombinators.Lawful

namespace Lax560851.StructuralCombinators.SizeLaws
end Lax560851.StructuralCombinators.SizeLaws

namespace Lax560851.StructuralCombinators.listFromRaw
end Lax560851.StructuralCombinators.listFromRaw

namespace Lax560851.StructuralCombinators.listToRaw
end Lax560851.StructuralCombinators.listToRaw

namespace Lax560851.StructuralCombinators.nat
end Lax560851.StructuralCombinators.nat

namespace Lax560851.StructuralCombinators.prod
end Lax560851.StructuralCombinators.prod

namespace Lax560851.StructuralCombinators

open Lax560851.StructuralPresentation

open Lax560851.StructuralPresentation.Presentation

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

end Lax560851.StructuralCombinators
end

-- Lax560851.CertifiedDerivation
noncomputable section
namespace Lax560851.CertifiedDerivation

open Lax560851.StructuralPresentation Lax560851.StructuralCombinators

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

end Lax560851.CertifiedDerivation
end

-- Lax560851.CertifiedDerivationElab
noncomputable section
namespace Lax560851.CertifiedDerivationElab

open Lax560851.StructuralPresentation Lax560851.StructuralCombinators

open Lax560851.CertifiedDerivation

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

end Lax560851.CertifiedDerivationElab
end

-- Lax560851.WordArena
noncomputable section
namespace Lax560851.WordArena
end Lax560851.WordArena

namespace Lax560851.WordArena.WordImage
end Lax560851.WordArena.WordImage

namespace Lax560851.WordArena.encodeInto
end Lax560851.WordArena.encodeInto

namespace Lax560851.WordArena.WordImage.ChildAddress
end Lax560851.WordArena.WordImage.ChildAddress

namespace Lax560851.WordArena.WordImage.ReachableFrom
end Lax560851.WordArena.WordImage.ReachableFrom

namespace Lax560851.WordArena.WordImage.Represents
end Lax560851.WordArena.WordImage.Represents
end

-- Lax560851.FormulaExample
noncomputable section
namespace Lax560851.FormulaExample

open Lax560851.StructuralPresentation Lax560851.WordArena

/-- Propositional syntax with natural-number atom names. -/
inductive Formula where
  | atom (index : Nat)
  | neg (body : Formula)
  | conj (left right : Formula)

-- Expanded from Lax560851.CertifiedDerivationElab.deriveCertifiedEncoding
noncomputable def _root_.Lax560851.FormulaExample.formulaRaw.match_1.{u_1} :
  (motive : Lax560851.FormulaExample.Formula → Sort u_1) →
    (x : Lax560851.FormulaExample.Formula) →
      (h_1 : (index : Nat) → motive (Lax560851.FormulaExample.Formula.atom index)) →
        (h_2 : (body : Lax560851.FormulaExample.Formula) → motive (Lax560851.FormulaExample.Formula.neg body)) →
          (h_3 :
              (left right : Lax560851.FormulaExample.Formula) →
                motive (Lax560851.FormulaExample.Formula.conj left right)) →
            motive x :=
  fun (motive : Lax560851.FormulaExample.Formula → Sort u_1) (x : Lax560851.FormulaExample.Formula)
      (h_1 : (index : Nat) → motive (Lax560851.FormulaExample.Formula.atom index))
      (h_2 : (body : Lax560851.FormulaExample.Formula) → motive (Lax560851.FormulaExample.Formula.neg body))
      (h_3 :
        (left right : Lax560851.FormulaExample.Formula) → motive (Lax560851.FormulaExample.Formula.conj left right)) =>
    @Lax560851.FormulaExample.Formula.casesOn.{u_1} (fun (x : Lax560851.FormulaExample.Formula) => motive x) x
      (fun (index : Nat) => h_1 index) (fun (body : Lax560851.FormulaExample.Formula) => h_2 body)
      fun (left right : Lax560851.FormulaExample.Formula) => h_3 left right

noncomputable def _root_.Lax560851.FormulaExample.formulaRaw._f :
  (x : Lax560851.FormulaExample.Formula) →
    (f :
        @Lax560851.FormulaExample.Formula.below.{1}
          (fun (x : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) x) →
      Lax560851.StructuralPresentation.Raw :=
  fun (x : Lax560851.FormulaExample.Formula)
      (f :
        @Lax560851.FormulaExample.Formula.below.{1}
          (fun (x : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) x) =>
    Lax560851.FormulaExample.formulaRaw.match_1.{1}
      (fun (x : Lax560851.FormulaExample.Formula) =>
        @Lax560851.FormulaExample.Formula.below.{1}
            (fun (x : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) x →
          Lax560851.StructuralPresentation.Raw)
      x
      (fun (index : Nat)
          (x :
            @Lax560851.FormulaExample.Formula.below.{1}
              (fun (x : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw)
              (Lax560851.FormulaExample.Formula.atom index)) =>
        Lax560851.StructuralCombinators.Raw.constructor "atom"
          (@List.cons.{0} Lax560851.StructuralPresentation.Raw
            (@Lax560851.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} Nat Lax560851.StructuralPresentation.Raw.nat
              (∀ (n : Nat),
                @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.StructuralPresentation.Raw.nat n)
                  (Lax560851.StructuralPresentation.Raw.nat n))
              ((fun (index : Nat) => Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat) index) index)
            (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
      (fun (body : Lax560851.FormulaExample.Formula)
          (x :
            @Lax560851.FormulaExample.Formula.below.{1}
              (fun (x : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw)
              (Lax560851.FormulaExample.Formula.neg body)) =>
        Lax560851.StructuralCombinators.Raw.constructor "neg"
          (@List.cons.{0} Lax560851.StructuralPresentation.Raw x.1 (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
      (fun (left right : Lax560851.FormulaExample.Formula)
          (x :
            @Lax560851.FormulaExample.Formula.below.{1}
              (fun (x : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw)
              (Lax560851.FormulaExample.Formula.conj left right)) =>
        Lax560851.StructuralCombinators.Raw.constructor "conj"
          (@List.cons.{0} Lax560851.StructuralPresentation.Raw x.1.1
            (@List.cons.{0} Lax560851.StructuralPresentation.Raw x.2.1
              (@List.nil.{0} Lax560851.StructuralPresentation.Raw))))
      f

noncomputable def _root_.Lax560851.FormulaExample.formulaRaw :
  Lax560851.FormulaExample.Formula → Lax560851.StructuralPresentation.Raw :=
  fun (x : Lax560851.FormulaExample.Formula) =>
    @Lax560851.FormulaExample.Formula.brecOn.{1}
      (fun (x : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) x
      Lax560851.FormulaExample.formulaRaw._f

noncomputable def _root_.Lax560851.FormulaExample.formulaRaw.Laws :
  Prop :=
  ∀ (value : Lax560851.FormulaExample.Formula),
    @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw value)
      (Lax560851.FormulaExample.formulaRaw.match_1.{1}
        (fun (value : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) value
        (fun (index : Nat) =>
          Lax560851.StructuralCombinators.Raw.constructor "atom"
            (@List.cons.{0} Lax560851.StructuralPresentation.Raw
              (@Lax560851.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} Nat
                Lax560851.StructuralPresentation.Raw.nat
                (∀ (n : Nat),
                  @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.StructuralPresentation.Raw.nat n)
                    (Lax560851.StructuralPresentation.Raw.nat n))
                ((fun (index : Nat) => Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat) index) index)
              (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
        (fun (body : Lax560851.FormulaExample.Formula) =>
          Lax560851.StructuralCombinators.Raw.constructor "neg"
            (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw body)
              (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
        fun (left right : Lax560851.FormulaExample.Formula) =>
        Lax560851.StructuralCombinators.Raw.constructor "conj"
          (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw left)
            (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw right)
              (@List.nil.{0} Lax560851.StructuralPresentation.Raw))))

noncomputable def _root_.Lax560851.FormulaExample.formulaRaw._sunfold :
  Lax560851.FormulaExample.Formula → Lax560851.StructuralPresentation.Raw :=
  fun (x : Lax560851.FormulaExample.Formula) =>
    Lax560851.FormulaExample.formulaRaw.match_1.{1}
      (fun (x : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) x
      (fun (index : Nat) =>
        Lax560851.StructuralCombinators.Raw.constructor "atom"
          (@List.cons.{0} Lax560851.StructuralPresentation.Raw
            (@Lax560851.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} Nat Lax560851.StructuralPresentation.Raw.nat
              (∀ (n : Nat),
                @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.StructuralPresentation.Raw.nat n)
                  (Lax560851.StructuralPresentation.Raw.nat n))
              ((fun (index : Nat) => Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat) index) index)
            (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
      (fun (body : Lax560851.FormulaExample.Formula) =>
        Lax560851.StructuralCombinators.Raw.constructor "neg"
          (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw body)
            (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
      fun (left right : Lax560851.FormulaExample.Formula) =>
      Lax560851.StructuralCombinators.Raw.constructor "conj"
        (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw left)
          (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw right)
            (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))

theorem _root_.Lax560851.FormulaExample.formulaRaw.certified._proof_1 :
  ∀ (value : Lax560851.FormulaExample.Formula),
    @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw value)
      (Lax560851.FormulaExample.formulaRaw.match_1.{1}
        (fun (value : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) value
        (fun (index : Nat) =>
          Lax560851.StructuralCombinators.Raw.constructor "atom"
            (@List.cons.{0} Lax560851.StructuralPresentation.Raw
              (@Lax560851.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} Nat
                Lax560851.StructuralPresentation.Raw.nat
                (∀ (n : Nat),
                  @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.StructuralPresentation.Raw.nat n)
                    (Lax560851.StructuralPresentation.Raw.nat n))
                Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat index)
              (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
        (fun (body : Lax560851.FormulaExample.Formula) =>
          Lax560851.StructuralCombinators.Raw.constructor "neg"
            (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw body)
              (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
        fun (left right : Lax560851.FormulaExample.Formula) =>
        Lax560851.StructuralCombinators.Raw.constructor "conj"
          (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw left)
            (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw right)
              (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))) :=
  fun (value : Lax560851.FormulaExample.Formula) =>
    @Lax560851.FormulaExample.Formula.casesOn.{0}
      (fun (t : Lax560851.FormulaExample.Formula) =>
        ∀ (h : @Eq.{1} Lax560851.FormulaExample.Formula value t),
          @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw value)
            (Lax560851.FormulaExample.formulaRaw.match_1.{1}
              (fun (value : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) value
              (fun (index : Nat) =>
                Lax560851.StructuralCombinators.Raw.constructor "atom"
                  (@List.cons.{0} Lax560851.StructuralPresentation.Raw
                    (@Lax560851.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} Nat
                      Lax560851.StructuralPresentation.Raw.nat
                      (∀ (n : Nat),
                        @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.StructuralPresentation.Raw.nat n)
                          (Lax560851.StructuralPresentation.Raw.nat n))
                      ((fun (index : Nat) => Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat) index) index)
                    (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
              (fun (body : Lax560851.FormulaExample.Formula) =>
                Lax560851.StructuralCombinators.Raw.constructor "neg"
                  (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw body)
                    (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
              fun (left right : Lax560851.FormulaExample.Formula) =>
              Lax560851.StructuralCombinators.Raw.constructor "conj"
                (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw left)
                  (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw right)
                    (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))))
      value
      (fun (index : Nat)
          (h : @Eq.{1} Lax560851.FormulaExample.Formula value (Lax560851.FormulaExample.Formula.atom index)) =>
        @Eq.ndrec.{0, 1} Lax560851.FormulaExample.Formula (Lax560851.FormulaExample.Formula.atom index)
          (fun (value : Lax560851.FormulaExample.Formula) =>
            @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw value)
              (Lax560851.FormulaExample.formulaRaw.match_1.{1}
                (fun (value : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) value
                (fun (index : Nat) =>
                  Lax560851.StructuralCombinators.Raw.constructor "atom"
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw
                      (@Lax560851.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} Nat
                        Lax560851.StructuralPresentation.Raw.nat
                        (∀ (n : Nat),
                          @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.StructuralPresentation.Raw.nat n)
                            (Lax560851.StructuralPresentation.Raw.nat n))
                        ((fun (index : Nat) => Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat) index) index)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
                (fun (body : Lax560851.FormulaExample.Formula) =>
                  Lax560851.StructuralCombinators.Raw.constructor "neg"
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw body)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
                fun (left right : Lax560851.FormulaExample.Formula) =>
                Lax560851.StructuralCombinators.Raw.constructor "conj"
                  (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw left)
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw right)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))))
          (@Eq.refl.{1} Lax560851.StructuralPresentation.Raw
            (Lax560851.FormulaExample.formulaRaw (Lax560851.FormulaExample.Formula.atom index)))
          value (@Eq.symm.{1} Lax560851.FormulaExample.Formula value (Lax560851.FormulaExample.Formula.atom index) h))
      (fun (body : Lax560851.FormulaExample.Formula)
          (h : @Eq.{1} Lax560851.FormulaExample.Formula value (Lax560851.FormulaExample.Formula.neg body)) =>
        @Eq.ndrec.{0, 1} Lax560851.FormulaExample.Formula (Lax560851.FormulaExample.Formula.neg body)
          (fun (value : Lax560851.FormulaExample.Formula) =>
            @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw value)
              (Lax560851.FormulaExample.formulaRaw.match_1.{1}
                (fun (value : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) value
                (fun (index : Nat) =>
                  Lax560851.StructuralCombinators.Raw.constructor "atom"
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw
                      (@Lax560851.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} Nat
                        Lax560851.StructuralPresentation.Raw.nat
                        (∀ (n : Nat),
                          @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.StructuralPresentation.Raw.nat n)
                            (Lax560851.StructuralPresentation.Raw.nat n))
                        ((fun (index : Nat) => Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat) index) index)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
                (fun (body : Lax560851.FormulaExample.Formula) =>
                  Lax560851.StructuralCombinators.Raw.constructor "neg"
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw body)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
                fun (left right : Lax560851.FormulaExample.Formula) =>
                Lax560851.StructuralCombinators.Raw.constructor "conj"
                  (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw left)
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw right)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))))
          (@Eq.refl.{1} Lax560851.StructuralPresentation.Raw
            (Lax560851.FormulaExample.formulaRaw (Lax560851.FormulaExample.Formula.neg body)))
          value (@Eq.symm.{1} Lax560851.FormulaExample.Formula value (Lax560851.FormulaExample.Formula.neg body) h))
      (fun (left right : Lax560851.FormulaExample.Formula)
          (h : @Eq.{1} Lax560851.FormulaExample.Formula value (Lax560851.FormulaExample.Formula.conj left right)) =>
        @Eq.ndrec.{0, 1} Lax560851.FormulaExample.Formula (Lax560851.FormulaExample.Formula.conj left right)
          (fun (value : Lax560851.FormulaExample.Formula) =>
            @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw value)
              (Lax560851.FormulaExample.formulaRaw.match_1.{1}
                (fun (value : Lax560851.FormulaExample.Formula) => Lax560851.StructuralPresentation.Raw) value
                (fun (index : Nat) =>
                  Lax560851.StructuralCombinators.Raw.constructor "atom"
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw
                      (@Lax560851.CertifiedDerivation.CertifiedFieldEncoding.toRaw.{0} Nat
                        Lax560851.StructuralPresentation.Raw.nat
                        (∀ (n : Nat),
                          @Eq.{1} Lax560851.StructuralPresentation.Raw (Lax560851.StructuralPresentation.Raw.nat n)
                            (Lax560851.StructuralPresentation.Raw.nat n))
                        ((fun (index : Nat) => Lax560851.CertifiedDerivation.CertifiedFieldEncoding.nat) index) index)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
                (fun (body : Lax560851.FormulaExample.Formula) =>
                  Lax560851.StructuralCombinators.Raw.constructor "neg"
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw body)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))
                fun (left right : Lax560851.FormulaExample.Formula) =>
                Lax560851.StructuralCombinators.Raw.constructor "conj"
                  (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw left)
                    (@List.cons.{0} Lax560851.StructuralPresentation.Raw (Lax560851.FormulaExample.formulaRaw right)
                      (@List.nil.{0} Lax560851.StructuralPresentation.Raw)))))
          (@Eq.refl.{1} Lax560851.StructuralPresentation.Raw
            (Lax560851.FormulaExample.formulaRaw (Lax560851.FormulaExample.Formula.conj left right)))
          value
          (@Eq.symm.{1} Lax560851.FormulaExample.Formula value (Lax560851.FormulaExample.Formula.conj left right) h))
      (@Eq.refl.{1} Lax560851.FormulaExample.Formula value)

noncomputable def _root_.Lax560851.FormulaExample.formulaRaw.certified :
  Lax560851.CertifiedDerivation.CertifiedFieldEncoding.{0} Lax560851.FormulaExample.Formula
    Lax560851.FormulaExample.formulaRaw Lax560851.FormulaExample.formulaRaw.Laws :=
  @Lax560851.CertifiedDerivation.CertifiedFieldEncoding.ofLaws.{0} Lax560851.FormulaExample.Formula
    Lax560851.FormulaExample.formulaRaw Lax560851.FormulaExample.formulaRaw.Laws
    Lax560851.FormulaExample.formulaRaw.certified._proof_1

/-- The formula $p_0 \land \neg p_1$. -/
def sample : Formula := .conj (.atom 0) (.neg (.atom 1))

/-- Constructor structure, before choosing a word-memory layout. -/
def sampleStructure : Raw := formulaRaw sample

end Lax560851.FormulaExample
end
