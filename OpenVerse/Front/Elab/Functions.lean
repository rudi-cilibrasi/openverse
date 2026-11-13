/- Elaboration of a program's field defaults and functions (phases 13–14 of
   `elabProgramCore`); public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Signatures

namespace OpenVerse.Front
open OpenVerse

/-- What each heap effect is, for messages. -/
def fxWhat : String → String
  | "reads" => "reads a var field"
  | "writes" => "sets a var field"
  | "allocates" => "constructs an object that has a var field or is <unique>"
  | k => k

/-- Refuses the first effect `st` has that the effects `allowed` of `name` do
    not, with what has it and what to write. -/
def fxCheck (name : String) (allowed : List String) (st : ESt) : Except String Unit := do
  -- writes first, then reads, then allocations
  let order := ["writes", "reads", "allocates"]
  for k in order do
    for (k', kp, via) in st.fx do
      if k' == k && !allowed.contains k then
        let what := match via with
          | some f => s!"{f}, which has the effect <{k}>"
          | none => fxWhat k
        let spec := if allowed.isEmpty then "<computes>" else String.intercalate "" (allowed.map (s!"<{·}>"))
        let fix := if allowed.isEmpty then "remove <computes>" else s!"add <{k}> or <transacts>"
        throw s!"{kp.show}: {name} {what}, which its effects ({spec}) do not allow: {fix}"

/-- What the elaboration of the fields' defaults gives (`elabFieldDefaults`). -/
structure FieldDefaults where
  /-- What they ask for: methods as values, lazily taken calls' functions and
      subtype dictionaries. -/
  needs : Requests
  /-- Each default's Verse Core code, with its struct's or class's name, its
      field's and its place, for `InitializerConvergence`. -/
  bodies : List (String × String × Pos × Expr)

/-- Construction effects and field defaults, a phase of `elabProgramCore`: a
    class whose objects are mutable or unique allocates, which its declared
    construction effects must allow; and each field default of the structs
    `tops` (classes' included) is elaborated once, with its struct's type
    parameters opaque, and must have only the effects its construction
    allows. -/
def elabFieldDefaults (env : TyEnv) (sigs : Signatures) (tops : List STop) (cdefs : List CDef) :
    Except String FieldDefaults := do
  let allSigs := sigs.all
  -- A mutable or unique instance needs allocation even when no source
  -- expression uses the type. Inherited mutable fields/identity count too.
  for cd in cdefs do
    if let some allowed := env.constructionFx[cd.name]? then
      if env.isUnique cd.name || (env.fields cd.name).any (fun (f, _, _) => env.isVarField cd.name f) then
        fxCheck s!"construction of {cd.name}" allowed
          { fx := [("allocates", cd.pos, none)] }
  let mut fieldNeeds : Requests := {}
  let mut initializerBodies : List (String × String × Pos × Expr) := []
  -- check every field default once, with its struct's type parameters opaque
  -- (a default is elaborated again, at its field's type, at each construction
  -- that omits the field)
  for t in tops do
    match t with
    | .const _ n none (.structDef _ _ _ _) =>
      let nps := ((env.sparams.lookup n).getD []).map fun (v, c) => Ty.param v c
      let senv := { env with
        tvars := (env.sparams.lookup n).getD [] |>.map fun (v, c) => (v, Ty.param v c)
        boundFacts := (env.sbounds.lookup n).getD [] }
      let allowed := env.constructionFx[n]?.getD heapFx
      let ctx : Ctx := { sigs := allSigs, sigProg := sigs.prog, types := senv, canFail := true,
                          fnFx := allowed, inDefaultCheck := true }
      for (f, ft, d) in (env.structs.lookup n).getD [] do
        if let some d := d then
          -- (an inherited default sees its home class's type parameters, #39)
          let home := (env.defaultHome.lookup (n, f)).getD n
          let hσ := (((env.sparams.lookup home).getD []).map (·.1)).zip (env.argsAt n nps home)
          let ctx := { ctx with defaults := [(n, f)], types := { senv with tvars := hσ } }
          match (do coerce d.pos (← elabE ctx d (some ft)) ft : EM Expr).run { env } with
          | .ok (body, st) =>
            fxCheck s!"default of field '{f}' of {n}" allowed st
            initializerBodies := initializerBodies ++ [(n, f, d.pos, body)]
            fieldNeeds := fieldNeeds.merge { methods := st.needs.methods, loops := st.needs.loops, subtypes := st.needs.subtypes }
          | .error msg => throw s!"{msg} (in the default of field '{f}' of {n})"
    | _ => pure ()
  return { needs := fieldNeeds, bodies := initializerBodies }

end OpenVerse.Front
