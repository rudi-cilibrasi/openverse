/-
  OpenVerse front end — fields with accessors (Book of Verse ch. 10,
  "Fields with Accessors"; ch. 12, "Getter and Setter Accessors"; the rules
  and the design are in docs/research/accessors.md).

  `var X<getter(G)><setter(S)>:t = external{}` in a class or an interface
  is a field with no storage: a read of it is a call of its class's method
  `G(:accessor):t`, a `set` of it one of `S(:accessor, :t):void`, and a path
  into its value (`O.X[I]`, `O.X.F`, up to an object) one call of the
  overload of `G` or `S` that takes the path's indices and field names after
  the accessor. This pass checks the declarations, as written, and gives the
  elaborator what it reads: each such field keeps its specifiers (the
  classes' phase sets it apart from the stored fields, `CDef.accessors`), its
  default `external{}` becomes the specifier `external`, and the type
  `accessor` of the accessors' first parameter is the struct `$accessor`,
  which no program can name, so that only a field's reads and writes call
  them (`Elab/Accessors.lean`).
-/
import OpenVerse.Front.TypeValues

namespace OpenVerse.Front
namespace Accessors

/-- The method a specifier `getter(G)` or `setter(S)` names (`kind`). -/
def named? (kind : String) (specs : List String) : List String :=
  specs.filterMap fun sp =>
    if sp.startsWith (kind ++ "(") && sp.endsWith ")" then
      some ((sp.drop (kind.length + 1)).dropEnd 1).toString
    else none

/-- Whether a field has accessors. -/
def isAccessorField (f : SField) : Bool :=
  !(named? "getter" f.specs).isEmpty || !(named? "setter" f.specs).isEmpty

/-- The struct of an accessor's first parameter, `(:accessor)`. -/
def accessorStruct : String := "$accessor"

/-- The specifier that says a field with accessors has the default
    `external{}`, so that a construction need not give it. -/
def externalSpec : String := "external"

/-- Whether a method's first parameter is the accessor, `(:accessor)`. -/
def takesAccessor (ps : List SParam) : Bool :=
  match ps with
  | q :: _ => q.ty == .name "accessor"
  | [] => false

/-- The program with its fields with accessors checked and written for the
    elaborator (the file's comment); unchanged when it has none. -/
def desugar (tops : List STop) : Except String (List STop) := do
  let classes : List (String × Pos × List String × Bool × List SField × List STop) := tops.filterMap fun
    | .classDef p n _ _ _ parents isI fs ms =>
      some (n, p, parents.filterMap (fun | .name m => some m | .app m _ => some m | _ => none), isI, fs, ms)
    | _ => none
  let usesAccessorType := tops.any fun
    | .classDef _ _ _ _ _ _ _ _ ms => ms.any fun | .fn _ _ ps .. => takesAccessor ps | _ => false
    | .fn _ _ ps .. => takesAccessor ps
    | _ => false
  let hasAccessors := classes.any fun (_, _, _, _, fs, _) => fs.any isAccessorField
  if !hasAccessors && !usesAccessorType then return tops
  -- (a parent as its class's module writes it, `c` or `M.c`: the class it
  -- names, from the module outward, as `TypeValues` reads it)
  let names : List String := classes.map (·.1)
  let resolve (owner p : String) : String :=
    let p := p.replace "." "::"
    let mods := (owner.splitOn "::").dropLast
    let cands := (List.range (mods.length + 1)).reverse.map fun k =>
      "::".intercalate (mods.take k ++ [p])
    (cands.find? names.contains).getD p
  let parentsOf (n : String) : List String :=
    match classes.find? (·.1 == n) with
    | some (_, _, ps, _, _, _) => ps.map (resolve n)
    | none => []
  let rec supersOf (fuel : Nat) (n : String) : List String :=
    match fuel with
    | 0 => [n]
    | fuel + 1 => n :: (parentsOf n).flatMap (supersOf fuel)
  let supers (n : String) : List String := (supersOf (classes.length + 1) n).eraseDups
  let below (n : String) : List String := names.filter fun d => d != n && (supers d).contains n
  -- (the methods a class or interface defines, by name: `(q:)M` is `M`)
  let bare (m : String) : String := match m.splitOn ":)" with
    | [_, b] => b
    | _ => m
  let methodsOf (n : String) : List (Pos × String × List SParam × List String × STy) :=
    match classes.find? (·.1 == n) with
    | some (_, _, _, _, _, ms) => ms.filterMap fun
        | .fn p m ps _ specs r _ => some (p, bare m, ps, specs, r)
        | _ => none
    | none => []
  let accessorsIn (n : String) : List SField :=
    match classes.find? (·.1 == n) with
    | some (_, _, _, _, fs, _) => fs.filter isAccessorField
    | none => []
  -- the program's own functions of a field's accessors' names
  let topFns : List String := tops.filterMap fun | .fn _ n .. => some n | _ => none
  for (c, p, _, _, fs, _) in classes do
    for f in fs.filter isAccessorField do
      let what := s!"{p.show}: {f.name} is a field with accessors (Book of Verse ch. 10, \"Fields with Accessors\")"
      let [g] := named? "getter" f.specs | throw s!"{what}: it needs one <getter(…)> and one <setter(…)>"
      let [s] := named? "setter" f.specs | throw s!"{what}: it needs one <getter(…)> and one <setter(…)>"
      -- (no storage: no value of its own, ch. 12: "The field must have
      -- `= external{}` or no default value")
      match f.default with
      | none | some (.construct _ "external" [] []) => pure ()
      | some _ => throw s!"{what}: it has no storage, so no value of its own: write = external\{} or nothing, and give it in each construction"
      -- (ch. 12: "Not all types are supported for accessor fields"; the
      -- Book's tests refuse a tuple, CustomClassVarAccessors.versetest:88)
      if let .tup _ := f.ty then
        throw s!"{what}: a field with accessors cannot be of a tuple type, {TypeValues.writtenTy f.ty}"
      -- its accessors: methods of its class or of one above it (the Book's
      -- tests refuse functions, CustomClassVarAccessors.versetest:103)
      let up := supers c
      let defined (m : String) := up.flatMap fun d => (methodsOf d).filter (·.2.1 == m)
      for (kind, m) in [("getter", g), ("setter", s)] do
        if (defined m).isEmpty then
          let where_ := if topFns.contains m then s!"{m} is a function, not a method" else s!"{c} has no method {m}"
          throw s!"{what}: its {kind} is a method of {c} or of a class or interface above it, and {where_}"
        -- (each overload takes the accessor first)
        for (mp, _, ps, _, _) in defined m do
          if !takesAccessor ps then
            throw s!"{mp.show}: {m} is the {kind} of {f.name}, so it takes the accessor first: {m}(:accessor, …)"
      -- (the getter and the setter of the field itself, at its type exactly,
      -- CustomClassVarAccessors.versetest 67-77, 699-713)
      let getterOk := (defined g).any fun (_, _, ps, _, r) => ps.length == 1 && r == f.ty
      if !getterOk then
        throw s!"{what}: its getter is {g}(:accessor):{TypeValues.writtenTy f.ty}, which {c} does not have"
      let setterOk := (defined s).any fun (_, _, ps, _, r) =>
        ps.length == 2 && (ps.getD 1 default).ty == f.ty && r == .name "void"
      if !setterOk then
        throw s!"{what}: its setter is {s}(:accessor, :{TypeValues.writtenTy f.ty}):void, which {c} does not have"
      -- (not overridden, ch. 10: "a field with accessors declared in an
      -- interface cannot be overridden in an implementing class. The accessor
      -- implementation is fixed by the interface"; ch. 12: "Fields with
      -- accessors cannot be overridden in subclasses")
      for d in below c do
        match classes.find? (·.1 == d) with
        | some (_, dp, _, _, dfs, _) =>
          if dfs.any (·.name == f.name) then
            throw s!"{dp.show}: {d} cannot override {f.name}, a field with accessors of {c}: its accessors are fixed where it is declared"
          for (mp, m, _, _, _) in methodsOf d do
            if m == g || m == s then
              throw s!"{mp.show}: {d} cannot override {m}, an accessor of {c}'s field {f.name}: its accessors are fixed where the field is declared"
        | none => pure ()
      -- (an override gives a field of a class or interface above accessors:
      -- one with accessors there is refused above; the type is the same)
      if f.specs.contains "override" then
        let inherited := (up.drop 1).findSome? fun d =>
          match classes.find? (·.1 == d) with
          | some (_, _, _, _, dfs, _) => dfs.find? (·.name == f.name)
          | none => none
        match inherited with
        | some h =>
          if h.ty != f.ty then
            throw s!"{what}: it overrides {f.name}:{TypeValues.writtenTy h.ty}, so its type is {TypeValues.writtenTy h.ty}"
        | none => throw s!"{what}: {f.name}<override> overrides no field of a class or interface above {c}"
  let _ := accessorsIn
  -- the accessor's type, a struct no program names, unless the program
  -- defines its own `accessor`
  let ownAccessor := tops.any fun
    | .classDef _ n .. | .const _ n .. => n == "accessor"
    | _ => false
  let g : STy → STy := STy.mapTy fun
    | .name "accessor" => if ownAccessor then .name "accessor" else .name accessorStruct
    | t => t
  let fieldOf (f : SField) : SField :=
    if !isAccessorField f then f else
    match f.default with
    | some (.construct _ "external" [] []) => { f with default := none, specs := f.specs ++ [externalSpec] }
    | _ => f
  let tops := tops.map fun
    | .classDef p n nsp tps specs parents isI fs ms =>
      STop.mapAll g id (.classDef p n nsp tps specs parents isI (fs.map fieldOf) ms)
    | t => STop.mapAll g id t
  let p0 : Pos := { line := 0, col := 0 }
  return (if ownAccessor then [] else [.const p0 accessorStruct [] none (.structDef p0 [] [] [])]) ++ tops

end Accessors
end OpenVerse.Front
