module
public meta import Lean

public meta section

/- Build-only RPC: inspect the elaborated operator, not the result type of
   the surrounding expression or a notation macro's source location. -/
open Lean Elab Meta Server RequestM

namespace LaxWebsiteNotation

structure Operator where
  name : String
  moduleName : String
  line : Nat
  type : String
  deriving FromJson, ToJson

@[server_rpc_method]
def operatorInfo (p : Lsp.Position) : RequestM (RequestTask (Option Operator)) := do
  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos p
  mapTaskCostly (findInfoTreeAtPos doc pos (includeStop := false)) fun tree? => do
    let some tree := tree? | return none
    let some info ← tree.hoverableInfoAtM? (m := IO) pos | return none
    let .ofTermInfo ti := info.info | return none
    info.ctx.runMetaM ti.lctx do
      let expr ← instantiateMVars ti.expr
      let head := expr.getAppFn.consumeMData
      let .const name _ := head | return none
      let mut operator := head
      -- Specialize implicit type and instance arguments, but retain the
      -- explicit operands: e.g. Nat → Nat → Nat, not just Nat, for `+`.
      for arg in expr.getAppArgs do
        let .forallE _ _ _ binder ← whnf (← inferType operator) | break
        if binder.isExplicit then break
        operator := mkApp operator arg
      let type ← ppExpr (← instantiateMVars (← inferType operator))
      let moduleName := (← findModuleOf? name).map Name.toString |>.getD ""
      let some ranges ← findDeclarationRanges? name | return none
      return some {
        name := name.toString
        moduleName
        line := ranges.selectionRange.pos.line
        type := type.pretty }

end LaxWebsiteNotation
