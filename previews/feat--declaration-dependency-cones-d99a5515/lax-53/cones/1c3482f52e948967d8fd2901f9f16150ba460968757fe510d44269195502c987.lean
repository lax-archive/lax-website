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

/-- Regard a child slot of a particular symbol as a child slot of the whole
alphabet. -/
def ofSymbolIndex {A : RankedAlphabet.{u}} (a : A.Symbol)
    (i : Fin (A.rank a)) : ChildIndex A :=
  ⟨i, ⟨a, i.isLt⟩⟩

end ChildIndex

/-- The nodes occurring in a particular ranked tree. -/
inductive Node {A : RankedAlphabet.{u}} : Tree A → Type u
  | root {a : A.Symbol} {children : Fin (A.rank a) → Tree A} :
      Node (.node a children)
  | inChild {a : A.Symbol} {children : Fin (A.rank a) → Tree A}
      (i : Fin (A.rank a)) (p : Node (children i)) :
      Node (.node a children)

namespace Node

/-- The root node of a tree. -/
def rootOf {A : RankedAlphabet.{u}} : (t : Tree A) → Node t
  | .node _ _ => .root

/-- The symbol labelling a node. -/
def label {A : RankedAlphabet.{u}} : {t : Tree A} → Node t → A.Symbol
  | .node a _, .root => a
  | .node _ _, .inChild _ p => label p

/-- The `i`th child of a node, as a node of the same ambient tree. -/
def child {A : RankedAlphabet.{u}} :
    {t : Tree A} → (p : Node t) → Fin (A.rank p.label) → Node t
  | .node _ children, .root, i => .inChild i (rootOf (children i))
  | .node _ _, .inChild j p, i => .inChild j (child p i)

/-- `ChildAt i p q` says that `q` is the immediate child of `p` in the
alphabet-wide child slot `i`. -/
def ChildAt {A : RankedAlphabet.{u}} (i : ChildIndex A) {t : Tree A}
    (p q : Node t) : Prop :=
  ∃ j : Fin (A.rank p.label),
    ChildIndex.ofSymbolIndex p.label j = i ∧ q = child p j

end Node

/-- A language of ranked trees. -/
abbrev TreeLanguage (A : RankedAlphabet.{u}) := Set (Tree A)

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

open FirstOrder

open FirstOrder.Language

open FirstOrder.Language.Structure

open Lax52.MSOSyntax

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Extend a valuation by putting a newly bound variable at index zero. -/
def consVal {n : Nat} (x : M) (v : Fin n → M) : Fin (n + 1) → M :=
  Fin.cases x v

/-- Satisfaction of an MSO formula under first-order and monadic valuations. -/
def Realize : {n m : Nat} → Formula L n m → (Fin n → M) →
    (Fin m → Set M) → Prop
  | _, _, .falsum, _, _ => False
  | _, _, .equal t₁ t₂, v, _ => t₁.realize v = t₂.realize v
  | _, _, .rel r ts, v, _ => RelMap r (fun i => (ts i).realize v)
  | _, _, .mem t X, v, V => t.realize v ∈ V X
  | _, _, .or phi psi, v, V => Realize phi v V ∨ Realize psi v V
  | _, _, .neg phi, v, V => ¬Realize phi v V
  | _, _, .exFO phi, v, V => ∃ x : M, Realize phi (consVal x v) V
  | _, _, .exSO phi, v, V => ∃ X : Set M, Realize phi v (consVal X V)

end Lax52.MSOSemantics
end

-- Lax53.TreeStructure
noncomputable section
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

/-- The canonical first-order structure of a ranked tree. -/
@[implicit_reducible]
def treeStructure {A : RankedAlphabet.{u}} (t : Tree A) :
    (treeSignature A).Structure (Node t) where
  funMap f := nomatch f
  RelMap
    | .label a, xs => Node.label (xs 0) = a
    | .child i, xs => Node.ChildAt i (xs 0) (xs 1)

/-- Satisfaction of a closed MSO sentence by the canonical structure of a
ranked tree. -/
def TreeModels {A : RankedAlphabet.{u}} (t : Tree A)
    (phi : Lax52.MSOSyntax.Sentence (treeSignature A)) : Prop :=
  @Lax52.MSOSemantics.Realize (treeSignature A) (Node t) (treeStructure t) 0 0 phi
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)

/-- The ranked-tree language defined by an MSO sentence. -/
def sentenceLanguage {A : RankedAlphabet.{u}}
    (phi : Lax52.MSOSyntax.Sentence (treeSignature A)) : TreeLanguage A :=
  {t | TreeModels t phi}

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

/-- Largest natural-number payload occurring in a representation. -/
def maxNat : Raw → Nat
  | .nat n => n
  | .pair a b => max a.maxNat b.maxNat

/-- Every natural payload in a representation fits into a `w`-bit word. -/
def PayloadsFitInWord (raw : Raw) (w : Nat) : Prop :=
  raw.maxNat < 2 ^ w

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

/-- Package an injective structural map as a low-level presentation by
choosing a preimage on its range. This construction certifies no complexity
or constructor-structurality property of the supplied map. -/
noncomputable def presentationOf {α : Type u} (f : α → Raw) : Presentation α := by
  classical
  exact {
    toRaw := f
    fromRaw := fun raw =>
      if h : ∃ x, f x = raw then some (Classical.choose h) else none
  }

namespace Presentation

end Presentation

end Lax58.StructuralPresentation
end

-- Lax58.StructuralCombinators
noncomputable section
namespace Lax58.StructuralCombinators.Derivable
end Lax58.StructuralCombinators.Derivable

namespace Lax58.StructuralCombinators.Generated
end Lax58.StructuralCombinators.Generated

namespace Lax58.StructuralCombinators.Lawful
end Lax58.StructuralCombinators.Lawful

namespace Lax58.StructuralCombinators.SizeLaws
end Lax58.StructuralCombinators.SizeLaws

namespace Lax58.StructuralCombinators.listFromRaw
end Lax58.StructuralCombinators.listFromRaw

namespace Lax58.StructuralCombinators.listToRaw
end Lax58.StructuralCombinators.listToRaw

namespace Lax58.StructuralCombinators.nat
end Lax58.StructuralCombinators.nat

namespace Lax58.StructuralCombinators.prod
end Lax58.StructuralCombinators.prod

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
namespace Lax58.WordArena.WordImage.ChildAddress
end Lax58.WordArena.WordImage.ChildAddress

namespace Lax58.WordArena.WordImage.ReachableFrom
end Lax58.WordArena.WordImage.ReachableFrom

namespace Lax58.WordArena.WordImage.Represents
end Lax58.WordArena.WordImage.Represents

namespace Lax58.WordArena

open Lax58.StructuralPresentation

universe u

/-- A finite array of unbounded natural-number words. -/
abbrev WordMemory := Array Nat

/-- A closed word array together with its distinguished root address. -/
structure WordImage where
  memory : WordMemory
  root : Nat
  deriving DecidableEq

namespace WordImage

/-- The distinguished Lax-13 input tape: root, followed by all arena words. -/
def toInput (I : WordImage) : List Nat := I.root :: I.memory.toList

/-- Tag of a natural-payload block. -/
def natTag : Nat := 0

/-- Tag of a binary-pair block. -/
def pairTag : Nat := 1

end WordImage

/-- Append the postorder arena of a raw value and return its root address. -/
def encodeInto : Raw → WordMemory → WordMemory × Nat
  | .nat payload, memory =>
      let address := memory.size
      (memory.push WordImage.natTag |>.push payload |>.push 0, address)
  | .pair left right, memory =>
      let (memory, leftAddress) := encodeInto left memory
      let (memory, rightAddress) := encodeInto right memory
      let address := memory.size
      (memory.push WordImage.pairTag |>.push leftAddress |>.push rightAddress, address)

/-- Distinguished closed postorder arena of a structural value. -/
def encodeRaw (raw : Raw) : WordImage :=
  let (memory, root) := encodeInto raw #[]
  { memory, root }

/-- Distinguished arena of a value through a named structural presentation. -/
def encode {α : Type u} (P : Presentation α) (x : α) : WordImage :=
  encodeRaw (P.toRaw x)

end Lax58.WordArena
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

/-- Named structural presentation of ranked trees. -/
noncomputable def treePresentation (alphabet : RankedAlphabetCode) :
    Presentation (Tree alphabet.toRankedAlphabet) :=
  Lax58.StructuralPresentation.presentationOf (treeStructure alphabet)

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

end Lax53.TreeModelCheckingEncoding
end

-- Lax13.Ram
noncomputable section
namespace Lax13.Ram

/-- An instruction. The first cell named is the one written, and every
other number naming a cell is read; `set` is the only instruction
carrying a literal, and `jump`, `jzero` carry a program address. -/
inductive Instr
  /-- Set cell `a` to the literal `n`. -/
  | set (a n : ℕ)
  /-- Set cell `a` to the contents of the cell whose address cell `b`
  holds. -/
  | load (a b : ℕ)
  /-- Set the cell whose address cell `a` holds to the contents of cell
  `b`. -/
  | store (a b : ℕ)
  /-- Set cell `a` to the sum of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | add (a b c : ℕ)
  /-- Set cell `a` to the difference of cells `b` and `c`, truncated at
  zero rather than wrapping around. -/
  | sub (a b c : ℕ)
  /-- Set cell `a` to the product of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | mul (a b c : ℕ)
  /-- Set cell `a` to the quotient of cells `b` and `c`, rounding
  towards zero; division by zero yields zero. -/
  | div (a b c : ℕ)
  /-- Set cell `a` to the bitwise conjunction of cells `b` and `c`. -/
  | and (a b c : ℕ)
  /-- Set cell `a` to cell `b` shifted left by the number of bits cell
  `c` holds, wrapping around modulo `2 ^ w`; a shift by `w` or more
  yields zero. -/
  | shiftl (a b c : ℕ)
  /-- Set cell `a` to the bitwise complement `2 ^ w - 1 - m[b]` of cell
  `b` within the word length. -/
  | not (a b : ℕ)
  /-- Continue at instruction `l`. -/
  | jump (l : ℕ)
  /-- Continue at instruction `l` if cell `a` is zero. -/
  | jzero (a l : ℕ)
  /-- Halt. -/
  | halt
  /-- Read the next number of the input tape into cell `a`, or halt if
  the tape is exhausted. -/
  | read (a : ℕ)
  /-- Append the contents of cell `a` to the output tape. -/
  | write (a : ℕ)

/-- A program: a finite sequence of instructions, numbered from `0`. -/
abbrev Program : Type := List Instr

/-- A machine state: the program counter, the contents of every memory
cell, the part of the input tape not yet read, and the output tape
written so far. Memory is the only storage there is. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The memory `m` with cell `a` set to `v`, at word length `w`: the
address and the value written are both taken modulo `2 ^ w`. -/
def setCell (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a % 2 ^ w then v % 2 ^ w else m b

/-- The effect of one instruction on the state at word length `w`, or
`none` if it halts the machine, which a `halt` instruction and a read
from an exhausted input tape do. Every value produced is reduced modulo
`2 ^ w` and every address used is reduced modulo `2 ^ w`. -/
def Instr.effect (w : ℕ) : Instr → State → Option State
  | set a n, s => some { s with pc := s.pc + 1, mem := setCell w s.mem a n }
  | load a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (s.mem (b % 2 ^ w) % 2 ^ w)) }
  | store a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) }
  | add a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) }
  | sub a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) }
  | mul a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) }
  | div a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) }
  | and a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w))) }
  | shiftl a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) }
  | not a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (2 ^ w - 1 - s.mem (b % 2 ^ w)) }
  | jump l, s => some { s with pc := l }
  | jzero a l, s => some { s with pc := if s.mem (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | halt, _ => none
  | read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail }
  | write a, s =>
      some { s with pc := s.pc + 1, out := s.out ++ [s.mem (a % 2 ^ w) % 2 ^ w] }

/-- One step of the machine at word length `w`: fetch the instruction
the program counter points at and execute it. The result is `none` if
the machine has halted, which also happens when the program counter has
run past the program. -/
def step (w : ℕ) (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect w s

/-- The state after `t` steps at word length `w`, or `none` if the
machine halts before executing `t` instructions. -/
def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the input word on the input tape, the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  inp := x
  out := []

/-- Started on input `x` at word length `w`, the machine executes
exactly `t` instructions and then halts, having written the word `y` to
its output tape. -/
def RunsTo (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ s : State, run w p t (initState x) = some s ∧ step w p s = none ∧ s.out = y

end Lax13.Ram
end

-- Lax13.RamComputes
noncomputable section
namespace Lax13.RamComputes

open Lax13.Ram

/-- At word length `w`, on every admissible input `x`, the program halts
within `T x` steps with output `f x`. -/
def ComputesInTime (w : ℕ) (p : Program) (D : Set (List ℕ))
    (f : List ℕ → List ℕ) (T : List ℕ → ℕ) : Prop :=
  ∀ x ∈ D, ∃ t ≤ T x, RunsTo w p x (f x) t

end Lax13.RamComputes
end

-- Lax58.RamComplexity
noncomputable section
namespace Lax58.RamComplexity

open Lax13.Ram Lax13.RamComputes

open Lax58.StructuralPresentation Lax58.WordArena

universe u v

/-- Input size and payload magnitude for a specified presentation. -/
def inputMagnitudeUsing {α : Type u} (input : Presentation α) (x : α) : Nat :=
  (input.toRaw x).nodes + (input.toRaw x).maxNat + 1

/-- A natural-number result occupies one output word. -/
def natOutput (n : Nat) : List Nat := [n]

/-- One program for all inputs and all sufficient word widths, with explicit
encodings and exact instruction and word-capacity bounds. -/
def RamComputableWithinUsing {α : Type u} {β : Type v}
    (input : Presentation α) (output : β → List Nat)
    (f : α → β) (timeBound wordBound : α → Nat) : Prop :=
  ∃ program : Program,
    ∀ (x : α) (w : Nat),
      (input.toRaw x).PayloadsFitInWord w →
      3 * (input.toRaw x).nodes ≤ 2 ^ w →
      wordBound x ≤ 2 ^ w →
      ComputesInTime w program {(encode input x).toInput}
        (fun _ => output (f x)) (fun _ => timeBound x)

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

open Classical in
/-- Once the alphabet and sentence are fixed before program choice, the
specialized program receives only a tree and has linear tree-node time. This
existential statement makes no effective program-generation claim. -/
axiom exists_fixed_sentence_modelChecking
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) :
  ∃ timeCoefficient wordCoefficient : Nat,
    RamComputableWithinUsing (treePresentation alphabet) natOutput
      (fun t => if t ∈ sentenceLanguage phi then 1 else 0)
      (fun t => timeCoefficient * (treeSize t + 1))
      (fun t => wordCoefficient * inputMagnitudeUsing
        (treePresentation alphabet) t)

end Lax53.MSOLinearTime
end
