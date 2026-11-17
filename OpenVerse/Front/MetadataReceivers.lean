/- Typed receiver certificates in the metadata-only view of a function. -/
import OpenVerse.Front.Types
import OpenVerse.Core.Syntax

namespace OpenVerse.Front.MetadataReceivers
open OpenVerse

structure Projection where
  body : Expr
  extraSlots : Array Ty := #[]
  nonCellSlots : List Nat := []
  noCellReachSlots : List Nat := []
  deriving Inhabited

/-- A generic or dynamically boxed value can still denote the private cell.
    A nominal receiver is excluded only by the actual class hierarchy. -/
private def nonCell (env : TyEnv) : Ty → Bool
  | .param .. | .any | .dyn => false
  | .struct name _ => !env.isSub "$varcell" name
  | _ => true

private structure ReachState where
  active : Std.HashMap String Unit := {}
  done : Std.HashMap String Bool := {}

/-- Each query is a conjunction over all possible physical fields. A repeated
    active type closes a coinductive cycle, while every outgoing field is
    still checked by its active ancestor. Memoization stays inside one root
    query, so a provisional positive never escapes a failed ancestor. -/
private partial def proveNoReach (env : TyEnv) (fuel : Nat) (ty : Ty) : StateM ReachState Bool := do
  if !nonCell env ty then return false
  let key := reprStr ty
  let state ← get
  if let some answer := state.done[key]? then return answer
  if state.active.contains key then return true
  if fuel == 0 then return false
  set { state with active := state.active.insert key () }
  let children : Option (List Ty) := match ty with
    | .arr element | .opt element => some [element]
    | .tup fields => some fields
    | .map key value | .weakMap key value => some [key, value]
    | .struct name args =>
      if (env.structs.lookup name).isNone then none else
      if env.isRefClass name then
        let variants := ((env.concreteBelow name) ++ env.phs.filter (env.isSub · name)).eraseDups
        if variants.isEmpty then none else
          some (args ++ variants.flatMap fun actual =>
            (env.fieldsSeen name args actual).map (·.2.1))
      else some (args ++ (env.fields name args).map (·.2.1))
    | .param .. | .any | .dyn => none
    | _ => some []
  let mut answer := children.isSome
  for child in children.getD [] do
    if !(← proveNoReach env (fuel - 1) child) then
      answer := false
      break
  modify fun state => { state with
    active := state.active.erase key
    done := state.done.insert key answer }
  return answer

/-- A stronger certificate than a non-cell root: no private identity can be
    stored anywhere inside the value. Opaque types and growing instantiations
    stay unknown. Failure to prove this is never itself a source refusal. -/
def noCellReach (env : TyEnv) (ty : Ty) : Bool :=
  ((proveNoReach env 64 ty).run {}).1

/-- Heap field indices are physical. Inherited/interface layouts must all
    agree before a field type can certify a later receiver expression. -/
private def fieldType (env : TyEnv) (name : String) (args : List Ty) (index : Nat) : Option Ty := do
  if !env.isRefClass name then none else pure ()
  let variants := ((env.concreteBelow name) ++ env.phs.filter (env.isSub · name)).eraseDups
  let first :: rest := variants | none
  let field (actual : String) : Option Ty :=
    ((env.fieldsSeen name args actual)[index]?).map (·.2.1)
  let ty ← field first
  if rest.all (fun actual => (field actual).any (· == ty)) then some ty else none

private partial def valueType (env : TyEnv) : Value → Option Ty
  | .int _ => some .int
  | .logic _ => some .logic
  | .char _ => some .char
  | .float _ => some .float
  | .ref address => do
    let (name, _, _) ← env.protos[address]?
    return .struct name []
  | .tup values => .tup <$> values.mapM (valueType env)
  | .some value => .opt <$> valueType env value
  | .arr values => do
    let first ← values[0]?
    let ty ← valueType env first
    if values.all (fun value => (valueType env value).any (· == ty)) then some (.arr ty) else none
  | .none => none

/-- This is intentionally a small type transfer, not a second elaborator.
    Unknown call results and opaque parameters never create certificates. -/
private partial def infer (env : TyEnv) (types : Array Ty) : Expr → Option Ty
  | .local slot => types[slot]?
  | .lit value => valueType env value
  | .assign slot value => types[slot]? <|> infer env types value
  | .seq _ value => infer env types value
  | .heap (.get index) [receiver] => do
    let .struct name args ← infer env types receiver | none
    fieldType env name args index
  | .heap (.isTag _) [value] => infer env types value
  | .prim (.tupGet index) [value] => do
    let .tup fields ← infer env types value | none
    fields[index]?
  | .prim .index [values, _] => do
    let .arr ty ← infer env types values | none
    return ty
  | .prim .query [value] => do
    let .opt ty ← infer env types value | none
    return ty
  | .prim .mkSome [value] => .opt <$> infer env types value
  | .prim .mkTup values => .tup <$> values.mapM (infer env types)
  | .prim .mkArr values => do
    let first :: _ := values | none
    let ty ← infer env types first
    if values.all (fun value => (infer env types value).any (· == ty)) then some (.arr ty) else none
  | .ite _ yes no => do
    let ty ← infer env types yes
    if (infer env types no).any (· == ty) then some ty else none
  | _ => none

private structure State where
  types : Array Ty
  extraSlots : Array Ty := #[]
  nonCellSlots : List Nat := []

private partial def rewrite (env : TyEnv) (body : Expr) : StateM State Expr := do
  match body with
  | .assign slot value => return .assign slot (← rewrite env value)
  | .seq first next => return .seq (← rewrite env first) (← rewrite env next)
  | .prim op values => return .prim op (← values.mapM (rewrite env))
  | .call target values => return .call target (← values.mapM (rewrite env))
  | .ite condition yes no => return .ite (← rewrite env condition) (← rewrite env yes) (← rewrite env no)
  | .forE slot source filter inner =>
    return .forE slot (← rewrite env source) (← rewrite env filter) (← rewrite env inner)
  | .loop inner => return .loop (← rewrite env inner)
  | .ret value => return .ret (← rewrite env value)
  | .print value => return .print (← rewrite env value)
  | .heap op values =>
    let values ← values.mapM (rewrite env)
    let original := Expr.heap op values
    if let .new _ := op then return original
    let receiver :: rest := values | return original
    if let .local _ := receiver then return original
    let state ← get
    let some ty := infer env state.types receiver | return original
    if !nonCell env ty then return original
    let slot := state.types.size
    set { state with types := state.types.push ty
                     extraSlots := state.extraSlots.push ty
                     nonCellSlots := slot :: state.nonCellSlots }
    -- The receiver stays before every later operand, is evaluated once,
    -- and retains its ordinary metadata role. Only its cell exclusion is new.
    return .seq (.assign slot receiver) (.heap op (.local slot :: rest))
  | other => return other

/-- Append virtual locals only to the analysis view. The caller extends
    analysis frame sizes, never the emitted program, runtime slot types or
    source-frame ownership. Source admission and ordinary heap permissions
    are unchanged; the certificate excludes only private-cell payload taint. -/
def project (env : TyEnv) (slotTys : Array Ty) (body : Expr) : Projection := Id.run do
  let privateType := if env.classIx.isEmpty then env.classes.contains "$varcell"
    else env.classIx.contains "$varcell"
  if !privateType then
    return { body }
  let (body, state) := (rewrite env body).run { types := slotTys }
  return { body, extraSlots := state.extraSlots, nonCellSlots := state.nonCellSlots.reverse }

/-- Optional reachability proofs are separate from projection: callers can
    use identity-only certificates without traversing nominal field graphs. -/
def withReachability (env : TyEnv) (slotTys : Array Ty) (projection : Projection) : Projection := Id.run do
  let mut cache : Std.HashMap String Bool := {}
  let mut provedSlots := []
  for (ty, slot) in (slotTys ++ projection.extraSlots).toList.zipIdx do
    let key := reprStr ty
    let proved := match cache[key]? with
      | some proved => proved
      | none => noCellReach env ty
    cache := cache.insert key proved
    if proved then provedSlots := slot :: provedSlots
  return { projection with noCellReachSlots := provedSlots.reverse }

end OpenVerse.Front.MetadataReceivers
