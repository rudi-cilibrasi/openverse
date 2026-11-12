import OpenVerse.Front.Types

namespace OpenVerse.Front.ChoiceTypes

/-- A continuation can abstract the varying parts of an alternative's type
    instead of widening the value before the suffix uses it. Equal columns
    share one parameter, preserving equations between tuple/class arguments. -/
structure Plan where
  binding : Ty
  params : List (String × Bool)
  instances : List (List (String × Ty))

private abbrev Columns := List (List Ty × String × Bool)

private partial def abstract (env : TyEnv) (stem : String) (types : List Ty) :
    StateM Columns Ty := do
  let first := types.headD .void
  if types.all (· == first) then
    return types.foldl Ty.commonBounds first
  if let some children := types.mapM (fun | .arr t => some t | _ => none) then
    return .arr (← abstract env stem children)
  if let some children := types.mapM (fun | .opt t => some t | _ => none) then
    return .opt (← abstract env stem children)
  if let some children := types.mapM (fun | .map k v => some (k, v) | _ => none) then
    return .map (← abstract env stem (children.map (·.1)))
      (← abstract env stem (children.map (·.2)))
  let args? : Option (List (List Ty)) := match first with
    | .tup ts => types.mapM fun
      | .tup us => if us.length == ts.length then some us else none
      | _ => none
    | .struct name ts => types.mapM fun
      | .struct other us => if name == other && us.length == ts.length then some us else none
      | _ => none
    | _ => none
  if let some rows := args? then
    let args ← (List.range (rows.headD []).length).mapM fun j =>
      abstract env stem (rows.map fun row => row[j]!)
    match first with
    | .tup _ => return .tup args
    | .struct name _ => return .struct name args
    | _ => pure ()
  let columns ← get
  -- Ty's ordinary equality ignores comparable bounds. Column identity must
  -- include them, so reusing an equation never strengthens a constraint.
  if let some (_, name, bound) := columns.find? fun (column, _, _) => reprStr column == reprStr types then
    return .param name bound
  let name := stem ++ s!"_{columns.length}"
  let bound := types.all (Ty.comparable env)
  modify (· ++ [(types, name, bound)])
  return .param name bound

def generalize (env : TyEnv) (stem : String) (types : List Ty) : Option Plan := do
  if types.isEmpty then none else
    let (binding, columns) := (abstract env stem types).run []
    some {
      binding := binding
      params := columns.map fun (_, name, bound) => (name, bound)
      instances := (List.range types.length).map fun j =>
        columns.map fun (column, name, _) => (name, column[j]!) }

end OpenVerse.Front.ChoiceTypes
