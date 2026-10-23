-- Lax dependency cone
-- Lean: v4.30.0
-- Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f

import Mathlib.Data.Nat.Pairing

-- Lax58.StructuralPresentation
section
namespace Lax58.StructuralPresentation.Raw.nodes
end Lax58.StructuralPresentation.Raw.nodes

namespace Lax58.StructuralPresentation

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

end Lax58.StructuralPresentation
end

-- Lax58.StructuralCombinators
section
namespace Lax58.StructuralCombinators
end Lax58.StructuralCombinators

namespace Lax58.StructuralCombinators.Derivable
end Lax58.StructuralCombinators.Derivable

namespace Lax58.StructuralCombinators.Generated
end Lax58.StructuralCombinators.Generated

namespace Lax58.StructuralCombinators.Lawful
end Lax58.StructuralCombinators.Lawful

namespace Lax58.StructuralCombinators.Raw
end Lax58.StructuralCombinators.Raw

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

namespace Lax58.StructuralCombinators.Raw.constructorCharsCode
end Lax58.StructuralCombinators.Raw.constructorCharsCode

namespace Lax58.StructuralCombinators.Raw.fields
end Lax58.StructuralCombinators.Raw.fields
end

-- Lax58.StructuralDerivation
section
namespace Lax58.StructuralDerivation

open Lax58.StructuralPresentation

open Lax58.StructuralCombinators

universe u

/-- Low-level encoding of a non-recursive constructor field. Possessing an
instance alone confers no complexity-theoretic status. -/
class FieldEncoding (α : Type u) where
  toRaw : α → Raw

/-- Apply the selected primitive-field encoding. -/
def fieldRaw {α : Type u} [P : FieldEncoding α] (x : α) : Raw :=
  P.toRaw x

open Lean Meta Elab Term

open Lean.Parser.Term

private def isDirectRecursiveField (inductiveName : Name) (type : Expr) : Bool :=
  type.getAppFn.constName? == some inductiveName

private def isFiniteRecursiveFamily (inductiveName : Name) (type : Expr) : Bool :=
  match type with
  | .forallE _ domain body _ =>
      domain.getAppFn.constName? == some ``Fin &&
        body.getAppFn.constName? == some inductiveName
  | _ => false

private def structuralAlternative (indInfo : InductiveVal)
    (recursiveCall : TSyntax `term) (constructorName : Name) :
    TermElabM (TSyntax ``matchAlt) := do
  let constructor ← getConstInfoCtor constructorName
  forallTelescopeReducing constructor.type fun arguments _ => do
    let mut patternArguments := #[]
    for _ in *...indInfo.numParams do
      patternArguments := patternArguments.push (← `(_))
    let mut fields : Array (Ident × Expr) := #[]
    for i in *...constructor.numFields do
      let argument := arguments[indInfo.numParams + i]!
      let declaration ← argument.fvarId!.getDecl
      if declaration.binderInfo.isExplicit then
        let fieldName := mkIdent (← mkFreshUserName `field)
        fields := fields.push (fieldName, declaration.type)
        patternArguments := patternArguments.push fieldName
      else
        -- Intrinsic indices and dependent witnesses are implicit constructor
        -- arguments. They remain available to dependent pattern matching, but
        -- do not duplicate data already fixed by the indexed value and its
        -- explicit fields. A downstream `Presentation.Lawful` proof remains
        -- responsible for showing that this erasure loses no value.
        patternArguments := patternArguments.push (← `(_))
    let mut encodedFields : TSyntax `term ← `([])
    for (fieldName, fieldType) in fields.reverse do
      encodedFields ←
        if isDirectRecursiveField indInfo.name fieldType then
          `(($recursiveCall:term) $fieldName:ident :: $encodedFields:term)
        else if isFiniteRecursiveFamily indInfo.name fieldType then
          `(List.ofFn (fun i => ($recursiveCall:term) ($fieldName:ident i)) ++
              $encodedFields:term)
        else
          `(Lax58.StructuralDerivation.fieldRaw $fieldName:ident ::
              $encodedFields:term)
    let tag := constructor.name.eraseMacroScopes.getString!
    let rightHandSide ←
      `(Lax58.StructuralCombinators.Raw.constructor $(quote tag)
          $encodedFields:term)
    `(matchAltExpr|
      | @$(mkIdent constructor.name):ident $patternArguments:term* =>
          $rightHandSide:term)

/-- Derive one complete constructor-structural match. The caller supplies the
recursive function application so ordinary Lean termination checking remains
authoritative. -/
elab "structural% " value:term " using " recursiveCall:term : term => do
  let valueExpression ← elabTerm value none
  let valueType ← whnf (← inferType valueExpression)
  let some inductiveName := valueType.getAppFn.constName?
    | throwError "structural% expects an inductive value, got {valueType}"
  let indInfo ← getConstInfoInduct inductiveName
  let alternatives := (← indInfo.ctors.mapM
    (structuralAlternative indInfo recursiveCall)).toArray
  let generated ← `(match $value:term with $alternatives:matchAlt*)
  elabTerm generated (some (mkConst ``Raw))

/-- Derive a complete constructor-structural function from its expected
single-argument function type. Unlike an inner `match`, the generated
constructor clauses remain visible to Lean's equation compiler, which is
needed for nested recursive fields such as `Fin n → Tree`.

Example:
```
def treeRaw : Tree → Raw :=
  structuralFun% using treeRaw
```
-/
elab "structuralFun% " "using " recursiveCall:term : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let functionType ← whnf expectedType
  let .forallE _ valueType _resultType _ := functionType
    | throwError
        "structuralFun% expects a single-argument function type, got {expectedType}"
  let valueType ← whnf valueType
  let some inductiveName := valueType.getAppFn.constName?
    | throwError
        "structuralFun% expects an inductive argument type, got {valueType}"
  let indInfo ← getConstInfoInduct inductiveName
  let alternatives := (← indInfo.ctors.mapM
    (structuralAlternative indInfo recursiveCall)).toArray
  let generated ← `(fun $alternatives:matchAlt*)
  elabTerm generated (some expectedType)

end Lax58.StructuralDerivation
end
