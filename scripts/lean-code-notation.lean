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

namespace LaxWebsiteCones

structure Declaration where
  name : String
  command : Nat
  start : Option Lsp.Position
  stop : Option Lsp.Position
  dependencies : Array String
  deriving FromJson, ToJson

structure Command where
  start : Lsp.Position
  stop : Lsp.Position
  kind : String
  uses : Array String
  expanded : Option String := none
  deriving FromJson, ToJson

structure Reference where
  name : String
  start : Lsp.Position
  stop : Lsp.Position
  deriving FromJson, ToJson

structure Module where
  declarations : Array Declaration
  commands : Array Command
  namespaces : Array String
  references : Array Reference := #[]
  deriving FromJson, ToJson

private def constants (ci : ConstantInfo) : NameSet := Id.run do
  let mut names := ci.getUsedConstantsAsSet
  if let .inductInfo v := ci then
    for name in v.ctors do names := names.insert name
  return names

private partial def infoConstants (tree : InfoTree) (names : NameSet := {}) : NameSet :=
  match tree with
  | .context _ child => infoConstants child names
  | .node info children =>
    let names := match info with
      | .ofTermInfo ti => ti.expr.getUsedConstants.foldl (fun s n => s.insert n) names
      | .ofFieldInfo fi => names.insert fi.projName
      | _ => names
    children.foldl (fun s child => infoConstants child s) names
  | .hole _ => names

private partial def infoReferences (text : FileMap) (tree : InfoTree)
    (refs : Array Reference := #[]) : Array Reference := Id.run do
  match tree with
  | .context _ child => return infoReferences text child refs
  | .node info children =>
    let mut refs := refs
    if let .ofTermInfo ti := info then
      if !ti.isBinder && ti.stx.isIdent && (ti.stx.getHeadInfo matches .original ..) then
        if let .const name _ := ti.expr.getAppFn then
          if let some range := ti.stx.getRange? then
            refs := refs.push {
              name := name.toString
              start := text.utf8PosToLspPos range.start
              stop := text.utf8PosToLspPos range.stop }
    return children.foldl (fun rs child => infoReferences text child rs) refs
  | .hole _ => return refs

/-- A command elaborator may depend on initializers from a different module.
It cannot necessarily run after its implementation is inlined into this file.
For generated definitions, export the checked expressions instead. -/
private def expandDefinitions (names : Array Name) : MetaM (Option String) := do
  if names.isEmpty || names.any isPrivateName then return none
  let env ← getEnv
  -- The compiler adds a self-recursive runtime implementation to some safe
  -- definitions. It is not part of their kernel bodies and need not be emitted.
  let mut pending := names.filter fun name => match env.find? name with
    | some (.defnInfo { safety := .partial, .. }) => false
    | _ => true
  let omitted := names.filter (!pending.contains ·)
  if pending.any (fun name => (env.find? name).any fun ci =>
      ci.getUsedConstantsAsSet.toArray.any omitted.contains) then return none
  let mut result := #[]
  while !pending.isEmpty do
    let some name := pending.find? (fun name =>
      match env.find? name with
      | some ci => !ci.getUsedConstantsAsSet.toArray.any pending.contains
      | none => false) | return none
    let some ci := env.find? name | return none
    let (keyword, value) ← match ci with
      | .defnInfo v =>
        match v.safety with
        | .safe => pure ("noncomputable def", v.value)
        | .unsafe => pure ("unsafe def", v.value)
        | .partial => return none
      | .thmInfo v => pure ("theorem", v.value)
      | _ => return none
    let levels := if ci.levelParams.isEmpty then "" else
      ".{" ++ String.intercalate ", " (ci.levelParams.map Name.toString) ++ "}"
    let type := (← ppExpr ci.type).pretty
    let body := (← ppExpr value).pretty
    if type.contains '⋯' || body.contains '⋯' then
      throwError "expanded dependency declaration {name} exceeds the pretty-printer limit"
    result := result.push s!"{keyword} _root_.{name}{levels} :\n  {type.replace "\n" "\n  "} :=\n  {body.replace "\n" "\n  "}"
    pending := pending.filter (· != name)
  return some (String.intercalate "\n\n" result.toList)

/-- Record command boundaries and both kernel and source dependencies. The
source edges retain names used by tactics even if absent from the final term.
Whole commands keep structures, mutual blocks and their helpers together. -/
@[server_rpc_method]
def moduleInfo (_ : Lsp.Position) : RequestM (RequestTask Module) := do
  let doc ← readDoc
  mapTaskCostly doc.cmdSnaps.waitAll fun (snaps, _) => do
    let some last := snaps.getLast? | return { declarations := #[], commands := #[], namespaces := #[] }
    let env := last.env
    let some first := snaps[0]? | return { declarations := #[], commands := #[], namespaces := #[] }
    let imported := first.env
    let namespaces := env.getNamespaces.toArray.filter (fun n => !imported.isNamespace n)
      |>.qsort Name.lt |>.map Name.toString
    let coreCtx : Core.Context := { fileName := doc.meta.uri, fileMap := doc.meta.text }
    let mut declarations := #[]
    let mut commands := #[]
    let mut references := #[]
    let mut seen : NameSet := {}
    for snap in snaps do
      if snap.stx.isOfKind ``Lean.Parser.Module.header || Parser.isTerminalCommand snap.stx then continue
      let some range := snap.stx.getRange? | continue
      let trees := snap.cmdState.infoState.substituteLazy.get.trees
      let uses := trees.foldl (fun names tree => infoConstants tree names) ({} : NameSet)
      references := trees.foldl (fun refs tree => infoReferences doc.meta.text tree refs) references
      let names := snap.env.checked.get.constants.foldStage2 (fun ns n _ => ns.push n) #[]
        |>.filter (fun n => !seen.contains n) |>.qsort Name.lt
      for name in names do
        seen := seen.insert name
        let some ci := env.find? name | continue
        let (range, _) ← (findDeclarationRanges? (m := CoreM) name).toIO coreCtx { env }
        declarations := declarations.push {
          name := name.toString
          command := commands.size
          start := range.map (fun r => doc.meta.text.leanPosToLspPos r.selectionRange.pos)
          stop := range.map (fun r => doc.meta.text.leanPosToLspPos r.selectionRange.endPos)
          dependencies := (constants ci).toArray.qsort Name.lt |>.map Name.toString }
      let mut expanded := none
      if snap.stx.getKind.getRoot != `Lean then
        let options := ({} : Options).setBool `pp.all true |>.setBool `pp.notation false
          |>.setBool `pp.fieldNotation false |>.setBool `pp.match false
          |>.set `pp.maxSteps (1000000 : Nat)
        let (value, _) ← (MetaM.run' <| expandDefinitions names).toIO
          { coreCtx with options } { env }
        expanded := value
      commands := commands.push {
        start := doc.meta.text.utf8PosToLspPos range.start
        stop := doc.meta.text.utf8PosToLspPos range.stop
        kind := snap.stx.getKind.toString
        uses := uses.toArray.qsort Name.lt |>.map Name.toString
        expanded }
    return { declarations, commands, namespaces, references }

end LaxWebsiteCones
