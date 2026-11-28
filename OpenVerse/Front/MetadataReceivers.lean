/- Typed receiver certificates in the metadata-only view of a function. -/
import OpenVerse.Front.Types
import OpenVerse.Core.Syntax

namespace OpenVerse.Front.MetadataReceivers
open OpenVerse

structure Projection where
  body : Expr
  extraSlots : Array Ty := #[]
  nonCellSlots : List Nat := []
  deriving Inhabited

/-- A resolved source signature, indexed by its emitted Core function. Only
    the explicit source parameters precede hidden evidence/witness operands. -/
structure CallType where
  params : List Ty := []
  ret : Ty
  /-- Callee type parameter and its actual hidden witness operand. -/
  witnesses : List (String × Nat) := []
  deriving BEq, Inhabited

/-- A generic or dynamically boxed value can still denote the private cell.
    A nominal receiver is excluded only by the actual class hierarchy. -/
private def nonCell (env : TyEnv) : Ty → Bool
  | .param .. | .any | .dyn => false
  | .struct name _ => !env.isSub "$varcell" name
  | _ => true

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
    A generic result is instantiated only from its actual hidden witnesses,
    whose types record the instance chosen during source elaboration. Opaque
    callee parameters never become types in the caller's scope. -/
private partial def infer (env : TyEnv) (types : Array Ty)
    (fnReturns : Array (Option CallType)) : Expr → Option Ty
  | .local slot => types[slot]?
  | .lit value => valueType env value
  | .call target args => do
    let signature ← (fnReturns[target]?).getD none
    if signature.ret.params.isEmpty then return signature.ret
    if (signature.witnesses.map (·.1)).eraseDups.length != signature.witnesses.length then none else pure ()
    let substitution ← signature.witnesses.mapM fun (name, index) => do
      let value ← args[index]?
      let ty ← infer env types fnReturns value
      if ty.params.isEmpty then some (name, ty) else none
    let ty := signature.ret.subst substitution
    if ty.params.isEmpty then some ty else none
  | .assign slot value => types[slot]? <|> infer env types fnReturns value
  | .seq _ value => infer env types fnReturns value
  | .heap (.get index) [receiver] => do
    let .struct name args ← infer env types fnReturns receiver | none
    fieldType env name args index
  | .heap (.isTag _) [value] => infer env types fnReturns value
  | .prim (.tupGet index) [value] => do
    let .tup fields ← infer env types fnReturns value | none
    fields[index]?
  | .prim .index [values, _] => do
    let .arr ty ← infer env types fnReturns values | none
    return ty
  | .prim .mapGet [values, _] => do
    let .arr (.tup [_, ty]) ← infer env types fnReturns values | none
    return ty
  | .prim .query [value] => do
    let .opt ty ← infer env types fnReturns value | none
    return ty
  | .prim .mkSome [value] => .opt <$> infer env types fnReturns value
  | .prim .mkTup values => .tup <$> values.mapM (infer env types fnReturns)
  | .prim .mkArr values => do
    let first :: _ := values | none
    let ty ← infer env types fnReturns first
    if values.all (fun value => (infer env types fnReturns value).any (· == ty)) then some (.arr ty) else none
  | .ite _ yes no => do
    let ty ← infer env types fnReturns yes
    if (infer env types fnReturns no).any (· == ty) then some ty else none
  | _ => none

private structure State where
  types : Array Ty
  fnReturns : Array (Option CallType) := #[]
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
    let some ty := infer env state.types state.fnReturns receiver | return original
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
def project (env : TyEnv) (slotTys : Array Ty) (body : Expr)
    (fnReturns : Array (Option CallType) := #[]) : Projection := Id.run do
  let privateType := if env.classIx.isEmpty then env.classes.contains "$varcell"
    else env.classIx.contains "$varcell"
  if !privateType then
    return { body }
  let (body, state) := (rewrite env body).run { types := slotTys, fnReturns }
  return { body, extraSlots := state.extraSlots, nonCellSlots := state.nonCellSlots.reverse }

end OpenVerse.Front.MetadataReceivers
