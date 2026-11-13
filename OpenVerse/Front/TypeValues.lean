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

/-- The types a definition writes, each mapped by `f`. -/
partial def STy.mapTy (f : STy → STy) : STy → STy
  | .arr t => f (.arr (t.mapTy f))
  | .opt t => f (.opt (t.mapTy f))
  | .tup ts => f (.tup (ts.map (·.mapTy f)))
  | .map k v => f (.map (k.mapTy f) (v.mapTy f))
  | .app n ts => f (.app n (ts.map (·.mapTy f)))
  | .fn ps es r => f (.fn (ps.map (·.mapTy f)) es (r.mapTy f))
  | t => f t

/-- `e` with every type it writes (its declarations', constructions'
    arguments) mapped by `g`, and every expression by `f`, from the leaves up. -/
partial def SExpr.mapAll (g : STy → STy) (f : SExpr → SExpr) (e : SExpr) : SExpr :=
  let e : SExpr := match e with
    | .decl p n (some t) v x => .decl p n (some (g t)) v x
    | .construct p n ts es => .construct p n (ts.map g) es
    | e => e
  let e : SExpr := match e with
    | .structDef p tps specs fs =>
      .structDef p tps specs (fs.map fun fl => { fl with ty := g fl.ty, default := fl.default.map (SExpr.mapAll g f) })
    | e => Id.run (e.mapChildrenM fun c => pure (c.mapAll g f))
  f e

/-- A definition with its types mapped by `g` and its expressions by `f`. -/
partial def STop.mapAll (g : STy → STy) (f : SExpr → SExpr) : STop → STop
  | .fn p n ps tps specs r b =>
    .fn p n (ps.map fun q => { q with ty := g q.ty, default := q.default.map (SExpr.mapAll g f) }) tps specs (g r)
      (b.mapAll g f)
  | .const p n specs t v => .const p n specs (t.map g) (v.mapAll g f)
  | .classDef p n ns tps specs ps isI fs ms =>
    .classDef p n ns tps specs ps isI (fs.map fun fl => { fl with ty := g fl.ty, default := fl.default.map (SExpr.mapAll g f) })
      (ms.map (STop.mapAll g f))

namespace TypeValues

/-- The metatypes this pass writes as interfaces. -/
def kinds : List String := ["subtype", "castable_subtype", "concrete_subtype"]

/-- The interface of the metatype `k` of `A`: `subtype(A)`. -/
def ifaceName (k a : String) : String := s!"{k}({a})"

/-- The class of the value `C`. -/
def valueClass (c : String) : String := s!"$type:{c}"

/-- The kind and bound of a metatype's interface, `("subtype", "A")` of
    `subtype(A)`. -/
def bound? (n : String) : Option (String × String) := do
  let k ← kinds.find? fun k => n.startsWith (k ++ "(") && n.endsWith ")"
  return (k, ((n.drop (k.length + 1)).dropEnd 1).toString)

/-- The method of a cast through a value of `subtype(A)`. -/
def castMethod (a : String) : String := s!"$cast({a})"

/-- The method of a construction through a value of `concrete_subtype(A)`. -/
def makeMethod (a : String) : String := s!"$make({a})"

/-- The metatypes a type writes: `(subtype, A)` of `subtype(A)`. -/
partial def metatypes (t : STy) : List (String × String) :=
  match t with
  | .app k [.name a] => if kinds.contains k then [(k, a)] else []
  | .app _ ts | .tup ts => ts.flatMap metatypes
  | .arr u | .opt u => metatypes u
  | .map k v => metatypes k ++ metatypes v
  | .fn ps _ r => ps.flatMap metatypes ++ metatypes r
  | .name _ => []
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
    if h.startsWith "$type:" then .app p (.ident p (h.drop "$type:".length).toString) as b else f e
  | .member p (.construct _ h [] []) m =>
    if h.startsWith "$type:" then .member p (.ident p (h.drop "$type:".length).toString) m else f e
  | e => f e


/-- The program with its types as values written as classes and interfaces
    (the file's comment); unchanged when it has none. A class or interface
    named as a value is one when no local or function of that name is in
    scope, which Verse, without shadowing, makes the case wherever the class
    is in scope. -/
def desugar (tops : List STop) : Except String (List STop) := do
  -- the classes and interfaces, not parametric, with their parents
  let classes : List (String × Pos × List String × List String × Bool × List SField) := tops.filterMap fun
    | .classDef p n _ [] specs parents isI fs _ =>
      some (n, p, specs, parents.filterMap (fun | .name m => some m | _ => none), isI, fs)
    | _ => none
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
  let concrete : String → Bool := fun n =>
    let fieldsHaveDefaults : String → Bool := fun s =>
      match classes.find? (·.1 == s) with
      | some (_, _, _, _, _, fs) => fs.all (·.default.isSome)
      | none => true
    -- (a concrete class is one marked <concrete>, whose fields all have
    -- defaults: Book of Verse ch. 11, "concrete_subtype"; its tests,
    -- MetatypeConcreteSubtype.versetest:40, refuse a class that is not)
    match classes.find? (·.1 == n) with
    | some (_, _, specs, _, isI, _) => !isI && specs.contains "concrete" && (supers n).all fieldsHaveDefaults
    | none => false
  -- the metatypes the program writes, and the classes it names as values
  let mut targets : List (String × String) := []
  let mut usesType := false
  let collect (acc : List (String × String) × Bool) (t : STy) : List (String × String) × Bool :=
    t.foldNames (fun acc _ => acc) acc
  let _ := collect
  let allTys : List (Pos × STy) := tops.flatMap fun
    | .fn p _ ps _ _ r b => (r :: ps.map (·.ty) ++ declTys b).map (p, ·)
    | .const p _ _ t v => (t.toList ++ declTys v).map (p, ·)
    | .classDef p _ _ _ _ _ _ fs ms => (fs.map (·.ty) ++ fs.flatMap (fun f => (f.default.map declTys).getD [])).map (p, ·) ++
        ms.flatMap fun | .fn mp _ ps _ _ r b => (r :: ps.map (·.ty) ++ declTys b).map (mp, ·) | _ => []
  let mut wherePos : List ((String × String) × Pos) := []
  for (p, t) in allTys do
    for (k, a) in metatypes t do
      if !targets.contains (k, a) then targets := targets ++ [(k, a)]; wherePos := wherePos ++ [((k, a), p)]
    if t.mentions "type" then usesType := true
  let values : List String := (tops.flatMap valueNames).filter isClass |>.eraseDups
  if targets.isEmpty && !usesType && values.isEmpty then return tops
  -- (each metatype's argument: a class or an interface, Book of Verse
  -- tests, Subtype.versetest 104-126, 3509; openverse writes subtype(t) of
  -- no other type)
  for (k, a) in targets do
    let p := ((wherePos.lookup (k, a)).map (·.show ++ ": ")).getD ""
    if !isClass a then
      throw s!"{p}{k}({a}): openverse writes {k} of a class or an interface only, not of {a} (types as values: docs/research/types-as-values.md)"
  -- the interfaces: of each class above a target or a value, upwards closed
  -- (each after the classes above it, as a class is defined after its parents)
  let closure0 : List String := (targets.map (·.2) ++ values).flatMap supers |>.eraseDups
  let closure : List String := (closure0.toArray.qsort fun a b => (supers a).length < (supers b).length).toList
  let p0 : Pos := { line := 0, col := 0 }
  let root : STop := .classDef p0 "type" [] [] [] [] true [] []
  let subIfaces : List STop := closure.map fun a =>
    .classDef p0 (ifaceName "subtype" a) [] [] []
      (if (parentsOf a).isEmpty then [.name "type"] else (parentsOf a).map (.name <| ifaceName "subtype" ·))
      true [] [.fn p0 (castMethod a) [{ name := "X", ty := .name a }] [] ["decides", "$abstract"] (.name a) (.block p0 [])]
  -- (castable_subtype(A) of any A, whose values are the <castable> classes
  -- below it: Castable.versetest 91-135, "class1 is not castable, so cannot
  -- be assigned. The arg to castable_subtype is ok")
  let castIfaces : List STop := closure.map fun a =>
    .classDef p0 (ifaceName "castable_subtype" a) [] [] []
      (.name (ifaceName "subtype" a) :: (parentsOf a).map (.name <| ifaceName "castable_subtype" ·)) true [] []
  let concreteIfaces : List STop := closure.map fun a =>
    .classDef p0 (ifaceName "concrete_subtype" a) [] [] []
      (.name (ifaceName "subtype" a) :: (parentsOf a).map (.name <| ifaceName "concrete_subtype" ·)) true []
      [.fn p0 (makeMethod a) [] [] ["$abstract"] (.name a) (.block p0 [])]
  -- the classes of the values: each gives the casts of the classes above it,
  -- and, when `C{}` constructs it, their constructions
  let valueClasses : List STop := values.map fun c =>
    let ups := supers c
    let parents : List STy := [.name (ifaceName "subtype" c)] ++ (if castable c then [.name (ifaceName "castable_subtype" c)] else []) ++
      (if concrete c then [.name (ifaceName "concrete_subtype" c)] else [])
    let x : SExpr := .ident p0 "X"
    -- (a cast to an interface or class no class is below always fails, as
    -- openverse's `C[X]` would refuse to write)
    let inhabited := classes.any fun (d, _, _, _, isI, _) => !isI && (supers d).contains c
    let fails (a : String) : SExpr :=
      .block p0 [.decl p0 "$none" (some (.opt (.name a))) false (.ident p0 "false"), .query p0 (.ident p0 "$none")]
    let casts : List STop := ups.map fun a =>
      .fn p0 (castMethod a) [{ name := "X", ty := .name a }] [] ["override", "decides"] (.name a)
        (if inhabited then .app p0 (.ident p0 c) [x] true else fails a)
    let makes : List STop := if concrete c then (ups.map fun a =>
      .fn p0 (makeMethod a) [] [] ["override"] (.name a) (.construct p0 c [] [])) else []
    .classDef p0 (valueClass c) [] [] [] parents false [] (casts ++ makes)
  -- the program with its metatypes written as the interfaces, and its
  -- values as the objects of their classes
  let g : STy → STy := STy.mapTy fun
    | .app k [.name a] => if kinds.contains k then .name (ifaceName k a) else .app k [.name a]
    | t => t
  let f : SExpr → SExpr := fun
    | e@(.ident p n) => if values.contains n then .construct p (valueClass n) [] [] else e
    | e => e
  -- (a call's or cast's head and a member's object are no values)
  let tops := tops.map fun t => (STop.mapAll g (protectHeads f) t)
  return root :: subIfaces ++ castIfaces ++ concreteIfaces ++ valueClasses ++ tops

end TypeValues
end OpenVerse.Front
