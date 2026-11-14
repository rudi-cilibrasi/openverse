/-
  OpenVerse front end — types as values, written with classes (Book of Verse
  ch. 11, "Metatypes": `subtype(t)`, `castable_subtype(t)`,
  `concrete_subtype(t)`, `type`; the rules and the design are in
  docs/research/types-as-values.md).

  A class or interface `C` named as a value is an object of a class of its
  own, `$type:C`, made by the front end; the types of such values are
  interfaces the front end makes too, which mirror the classes:

  - `subtype(A)`, for each class or interface `A` above a value's class,
    below `subtype(P)` for each parent `P` of `A`, and below `type`, which
    every type value is; it declares the cast through the value,
    `$cast(A)(X:A)<decides>:A`, which `$type:C` gives as `C[X]`, so that
    `T[X]` with `T:subtype(A)` is `T.$cast(A)[A[X]]`;
  - `castable_subtype(A)`, below `subtype(A)`, which `$type:C` is when `C`
    is `<castable>`;
  - `concrete_subtype(A)`, below `subtype(A)`, which `$type:C` is when `C`
    is `<concrete>`, and which declares `$make(A)():A`, which `$type:C`
    gives as `C{}`, so that `T{}` with `T:concrete_subtype(A)` is
    `T.$make(A)()`.

  `subtype(A) <: subtype(B)` exactly when `A <: B`, as the Book's tests have
  it (`Subtype.versetest` 140-190), since the interfaces are below one
  another as the classes are; the classes `$type:C` are not `<unique>`, so
  type values are not compared, as the Book does not yet (its tests: "We
  can't yet compare the subtype values"). No Verse Core is added: these are
  ordinary classes, interfaces and methods.
-/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front

namespace TypeValues

/-- The metatypes this pass writes as interfaces. -/
def kinds : List String := ["subtype", "castable_subtype", "concrete_subtype"]

/-- The interface of the metatype `k` of `A`: `subtype(A)`. -/
def ifaceName (k a : String) : String := s!"{k}({a})"

/-- The mark of the `castable_subtype(A)` of a `<castable>` `A`. -/
def castableMark : String := "$castable"

/-- The class of the value `C`, `$type:C`. -/
def valuePrefix : String := "$type:"
def valueClass (c : String) : String := valuePrefix ++ c
/-- The class `C` whose value's class is `n`. -/
def valueClass? (n : String) : Option String := afterPrefix? valuePrefix n

/-- The kind and bound of a metatype's interface, `("subtype", "A")` of
    `subtype(A)`. -/
def bound? (n : String) : Option (String × String) := do
  let k ← kinds.find? fun k => n.startsWith (k ++ "(") && n.endsWith ")"
  return (k, ((n.drop (k.length + 1)).dropEnd 1).toString)

/-- The method of a cast through a value of `subtype(A)`. -/
def castMethod (a : String) : String := s!"$cast({a})"

/-- The method of a construction through a value of `concrete_subtype(A)`. -/
def makeMethod (a : String) : String := s!"$make({a})"

/-- A type as written: `[]int`, `c(int)`, `tuple(int, float)`; the names of
    the interfaces of metatypes of types other than classes. -/
partial def writtenTy : STy → String
  | .name n => n
  | .arr t => "[]" ++ writtenTy t
  | .opt t => "?" ++ writtenTy t
  | .tup ts => s!"tuple({", ".intercalate (ts.map writtenTy)})"
  | .map k v => s!"[{writtenTy k}]{writtenTy v}"
  | .app n ts => s!"{n}({", ".intercalate (ts.map writtenTy)})"
  | .fn ps _ r => s!"type\{_({", ".intercalate (ps.map fun p => ":" ++ writtenTy p)}):{writtenTy r}}"

/-- The metatypes a type writes: `(subtype, A)` of `subtype(A)`, with the
    type of its argument, as written. -/
partial def metatypes (t : STy) : List (String × STy) :=
  match t with
  | .app k [a] => if kinds.contains k then [(k, a)] else metatypes a
  | t => t.children.flatMap metatypes
/-- The types of the declarations of an expression. -/
partial def declTys (e : SExpr) : List STy :=
  match e with
  | .decl _ _ (some t) _ x => t :: declTys x
  | .construct _ _ ts es => ts ++ es.flatMap declTys
  | e => e.children.flatMap declTys
partial def exprValues (e : SExpr) : List String :=
  match e with
  | .ident _ n => [n]
  | .app _ (.ident _ _) as _ => as.flatMap exprValues
  | .member _ (.ident _ _) _ => []
  | e => e.children.flatMap exprValues

/-- The names an expression uses as values: its identifiers but a call's,
    a cast's or a member's head. -/
partial def valueNames : STop → List String
  | .fn _ _ ps _ _ _ b => ps.flatMap (fun q => (q.default.map exprValues).getD []) ++ exprValues b
  | .const _ _ _ _ v => exprValues v
  | .classDef _ _ _ _ _ _ _ fs ms => fs.flatMap (fun f => (f.default.map exprValues).getD []) ++
      ms.flatMap valueNames
/-- `f` but at a call's, a cast's or a member's head. -/
def protectHeads (f : SExpr → SExpr) (e : SExpr) : SExpr :=
  match e with
  | .app p (.construct _ h [] []) as b =>
    if let some c := valueClass? h then .app p (.ident p c) as b else f e
  | .member p (.construct _ h [] []) m =>
    if let some c := valueClass? h then .member p (.ident p c) m else f e
  | e => f e


/-- The program with its types as values written as classes and interfaces
    (the file's comment); unchanged when it has none. A class or interface
    named as a value is one when no local or function of that name is in
    scope, which Verse, without shadowing, makes the case wherever the class
    is in scope. -/
def desugar (tops : List STop) : Except String (List STop) := do
  -- the classes and interfaces, not parametric, with their parents
  let classes0 : List (String × Pos × List String × List String × Bool × List SField) := tops.filterMap fun
    | .classDef p n _ [] specs parents isI fs _ =>
      some (n, p, specs, parents.filterMap (fun | .name m => some m | _ => none), isI, fs)
    | _ => none
  -- (a parent as its class's module writes it, `c` or `M.c`: the class it
  -- names, from the module outward, `A::B::c`)
  let names : List String := classes0.map (·.1)
  let resolve (owner p : String) : String :=
    let p := p.replace "." "::"
    let mods := (owner.splitOn "::").dropLast
    let cands := (List.range (mods.length + 1)).reverse.map fun k =>
      "::".intercalate (mods.take k ++ [p])
    (cands.find? names.contains).getD p
  let classes := classes0.map fun (n, p, specs, ps, isI, fs) => (n, p, specs, ps.map (resolve n), isI, fs)
  let isClass (n : String) : Bool := classes.any (·.1 == n)
  let parentsOf (n : String) : List String :=
    match classes.find? (·.1 == n) with
    | some (_, _, _, ps, _, _) => ps
    | none => []
  let rec supersOf (fuel : Nat) (n : String) : List String :=
    match fuel with
    | 0 => [n]
    | fuel + 1 => n :: (parentsOf n).flatMap (supersOf fuel)
  let supers (n : String) : List String := (supersOf (classes.length + 1) n).eraseDups
  let castable (n : String) : Bool := (supers n).any fun s =>
    match classes.find? (·.1 == s) with
    | some (_, _, specs, _, _, _) => specs.contains "castable"
    | none => false
  -- (the fields `C{}` must give none of: its own and those above it)
  -- (a concrete class is one marked <concrete>, which needs a default for
  -- every field, inherited ones included, `classFields`: Book of Verse ch.
  -- 11, "concrete_subtype"; its tests, MetatypeConcreteSubtype.versetest:40,
  -- refuse a class that is not marked)
  let concrete : String → Bool := fun n =>
    match classes.find? (·.1 == n) with
    | some (_, _, specs, _, isI, _) => !isI && specs.contains "concrete"
    | none => false
  -- the metatypes the program writes, and the classes it names as values
  let mut targets : List (String × String) := []
  let mut argTys : List (String × STy) := []
  let mut usesType := false
  let allTys : List (Pos × STy) := tops.flatMap fun
    | .fn p _ ps _ _ r b => (r :: ps.map (·.ty) ++ declTys b).map (p, ·)
    | .const p _ _ t v => (t.toList ++ declTys v).map (p, ·)
    | .classDef p _ _ _ _ _ _ fs ms => (fs.map (·.ty) ++ fs.flatMap (fun f => (f.default.map declTys).getD [])).map (p, ·) ++
        ms.flatMap fun | .fn mp _ ps _ _ r b => (r :: ps.map (·.ty) ++ declTys b).map (mp, ·) | _ => []
  let mut wherePos : List ((String × String) × Pos) := []
  for (p, t) in allTys do
    for (k, argTy) in metatypes t do
      let a := writtenTy argTy
      if !targets.contains (k, a) then
        targets := targets ++ [(k, a)]; wherePos := wherePos ++ [((k, a), p)]; argTys := argTys ++ [(a, argTy)]
    if t.mentions "type" then usesType := true
  let values : List String := (tops.flatMap valueNames).filter isClass |>.eraseDups
  -- (the types other than classes and interfaces that a type value may be:
  -- the built-in ones, `true` and `false` as the Book's tests write them,
  -- the program's structs and enums, and arrays, options, maps and tuples
  -- of them)
  let typeNames : List String := ["int", "float", "logic", "char", "char32", "string", "rational", "void",
      "true", "false"] ++ tops.filterMap fun
    | .const _ n _ none (.structDef ..) | .const _ n _ none (.enumDef ..) => some n
    | _ => none
  let rec plainType (fuel : Nat) (t : STy) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      match t with
      | .name n => typeNames.contains n || isClass n
      | .arr u | .opt u => plainType fuel u
      | .map k v => plainType fuel k && plainType fuel v
      | .tup ts => ts.all (plainType fuel)
      | _ => false
  -- (the type names a program uses as values: their own classes' values)
  -- (not `true` and `false`, which as values are the logic values)
  let typeValues : List String := (tops.flatMap valueNames).filter (fun n =>
    typeNames.contains n && !isClass n && n != "true" && n != "false") |>.eraseDups
  -- (`any` and `comparable` as values: types, of `type`, with no metatype
  -- of their own, as `subtype(any)` is not written; the Book's tests pass
  -- them where a type is, `GetCastableFinalSuperClass.versetest` 302, 304)
  let topValues : List String := (tops.flatMap valueNames).filter (["any", "comparable"].contains ·) |>.eraseDups
  if targets.isEmpty && !usesType && values.isEmpty && typeValues.isEmpty && topValues.isEmpty then return tops
  -- (each metatype's argument: a class or an interface, Book of Verse
  -- tests, Subtype.versetest 104-126, 3509; `subtype(t)` also of another
  -- type, written of types, `subtype(int)`, `subtype([]c)`, Subtype.versetest
  -- 113-119, 140-142; `concrete_subtype(any)` and
  -- `concrete_subtype(comparable)`, MetatypeConcreteSubtype.versetest 12-35)
  let tops0 := (targets.filter fun (k, a) => !isClass a && (k != "concrete_subtype" || (a != "any" && a != "comparable")))
  for (k, a) in tops0 do
    let p := ((wherePos.lookup (k, a)).map (·.show ++ ": ")).getD ""
    let argTy := (argTys.lookup a).getD (.name a)
    if k == "subtype" && !plainType 8 argTy then
      throw s!"{p}subtype({a}): openverse writes subtype of a class, an interface, a built-in type, a struct, an enum, or an array, option, map or tuple of them, not of {a} (types as values: docs/research/types-as-values.md)"
    if k != "subtype" then
      throw s!"{p}{k}({a}): openverse writes {k} of a class or an interface only, not of {a} (types as values: docs/research/types-as-values.md)"
  let otherSubtypes : List String := ((tops0.map (·.2)) ++ typeValues).eraseDups
  let concreteTops : List String := ["any", "comparable"].filter fun a => targets.contains ("concrete_subtype", a)
  -- the interfaces: of each class above a target or a value, upwards closed
  -- (each after the classes above it, as a class is defined after its parents)
  let closure0 : List String := ((targets.map (·.2)).filter isClass ++ values).flatMap supers |>.eraseDups
  let closure : List String := (closure0.toArray.qsort fun a b => (supers a).length < (supers b).length).toList
  let p0 : Pos := { line := 0, col := 0 }
  let root : STop := .classDef p0 "type" [] [] ["computes"] [] true [] []
  let subIfaces : List STop := closure.map fun a =>
    .classDef p0 (ifaceName "subtype" a) [] [] ["computes"]
      (if (parentsOf a).isEmpty then [.name "type"] else (parentsOf a).map (.name <| ifaceName "subtype" ·))
      true [] [.fn p0 (castMethod a) [{ name := "X", ty := .name a }] [] ["decides", "computes", "$abstract"] (.name a) (.block p0 [])]
  -- (castable_subtype(A) of any A, whose values are the <castable> classes
  -- below it: Castable.versetest 91-135, "class1 is not castable, so cannot
  -- be assigned. The arg to castable_subtype is ok")
  -- (with the mark `$castable` when `A` itself is: a join of two values
  -- keeps castable_subtype(A) only then, Castable.versetest 145-168)
  let castIfaces : List STop := closure.map fun a =>
    .classDef p0 (ifaceName "castable_subtype" a) [] [] ["computes"]
      (.name (ifaceName "subtype" a) :: (parentsOf a).map (.name <| ifaceName "castable_subtype" ·) ++
        (if castable a then [.name castableMark] else [])) true [] []
  let concreteIfaces : List STop := closure.map fun a =>
    .classDef p0 (ifaceName "concrete_subtype" a) [] [] ["computes"]
      (.name (ifaceName "subtype" a) :: (parentsOf a).map (.name <| ifaceName "concrete_subtype" ·)) true []
      [.fn p0 (makeMethod a) [] [] ["$abstract"] (.name a) (.block p0 [])]
  -- (the metatypes of other types: below `type`, with no method: nothing
  -- reads such a value but a conversion to `type`)
  let otherIfaces : List STop := otherSubtypes.map fun a =>
    .classDef p0 (ifaceName "subtype" a) [] [] ["computes"] [.name "type"] true [] []
  -- (`concrete_subtype(any)`, `concrete_subtype(comparable)`: the values of
  -- the `<concrete>` classes, and of those that are `<unique>`, so
  -- comparable; with no construction, "comparable cannot be instanced here
  -- because we don't know if it's a class type", MetatypeConcreteSubtype
  -- .versetest:35, 3545)
  let unique (n : String) : Bool := (supers n).any fun s =>
    match classes.find? (·.1 == s) with
    | some (_, _, specs, _, _, _) => specs.contains "unique"
    | none => false
  let concreteOthers : List STop := concreteTops.map fun a =>
    .classDef p0 (ifaceName "concrete_subtype" a) [] [] ["computes"] [.name "type"] true [] []
  -- the classes of the values: each gives the casts of the classes above it,
  -- and, when `C{}` constructs it, their constructions; a value is made
  -- with no effect (`<computes>`: it has no field), and a cast through it
  -- has none (`$cast(A)`, `<computes>`), as a cast `C[X]` has none, so that
  -- a function of any effects may name a type and cast through it
  let valueClasses : List STop := values.map fun c =>
    let ups := supers c
    let parents : List STy := [.name (ifaceName "subtype" c)] ++ (if castable c then [.name (ifaceName "castable_subtype" c)] else []) ++
      (if concrete c == true then [.name (ifaceName "concrete_subtype" c)] else []) ++
      (if concrete c && concreteTops.contains "any" then [.name (ifaceName "concrete_subtype" "any")] else []) ++
      (if concrete c && unique c && concreteTops.contains "comparable" then [.name (ifaceName "concrete_subtype" "comparable")] else [])
    let x : SExpr := .ident p0 "X"
    -- (a cast to an interface or class no class is below always fails, as
    -- openverse's `C[X]` would refuse to write)
    let inhabited := classes.any fun (d, _, _, _, isI, _) => !isI && (supers d).contains c
    let fails (a : String) : SExpr :=
      .block p0 [.decl p0 "$none" (some (.opt (.name a))) false (.ident p0 "false"), .query p0 (.ident p0 "$none")]
    let casts : List STop := ups.map fun a =>
      .fn p0 (castMethod a) [{ name := "X", ty := .name a }] [] ["override", "decides", "computes"] (.name a)
        (if inhabited then .app p0 (.ident p0 c) [x] true else fails a)
    let makes : List STop := if concrete c == true then (ups.map fun a =>
      .fn p0 (makeMethod a) [] [] ["override"] (.name a) (.construct p0 c [] [])) else []
    .classDef p0 (valueClass c) [] [] ["computes"] parents false [] (casts ++ makes)
  -- (the values of other types: classes of their own, below their
  -- metatypes)
  let otherValueClasses : List STop := typeValues.map (fun n =>
    .classDef p0 (valueClass n) [] [] ["computes"] [.name (ifaceName "subtype" n)] false [] []) ++
    topValues.map fun n => .classDef p0 (valueClass n) [] [] ["computes"] [.name "type"] false [] []
  -- the program with its metatypes written as the interfaces, and its
  -- values as the objects of their classes
  let g : STy → STy := STy.mapTy fun
    | .app k [a] => if kinds.contains k then .name (ifaceName k (writtenTy a)) else .app k [a]
    | t => t
  let f : SExpr → SExpr := fun
    | e@(.ident p n) =>
      if values.contains n || typeValues.contains n || topValues.contains n then .construct p (valueClass n) [] [] else e
    | e => e
  -- (a call's or cast's head and a member's object are no values)
  let tops := tops.map fun t => (STop.mapAll g (protectHeads f) t)
  return root :: .classDef p0 castableMark [] [] ["computes"] [] true [] [] :: subIfaces ++ castIfaces ++ concreteIfaces ++
    otherIfaces ++ concreteOthers ++ valueClasses ++ otherValueClasses ++ tops

end TypeValues
end OpenVerse.Front
