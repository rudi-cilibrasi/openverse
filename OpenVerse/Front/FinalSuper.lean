/-
  OpenVerse front end — `GetCastableFinalSuperClass` and
  `GetCastableFinalSuperClassFromType` (Book of Verse ch. 11, "final_super
  and Type Queries"; the API reference, module `/Verse.org/Verse`; the rules
  are pinned in docs/research/classes-and-subtyping.md).

  `GetCastableFinalSuperClass[B, X]` gives the class `C` that is
  `<final_super>`, castable (`<castable>`, or below a `<castable>` class or
  interface), has `B` among its parents, and is `X`'s class or above it, as
  a value of `castable_subtype(B)`; it fails when there is none.
  `GetCastableFinalSuperClassFromType[B, T]` does the same for the class a
  type value `T` holds. `B` is a type written at the call. A class has one
  class chain, so at most one `C` has a class `B` as its parent; of those
  that list an interface `B`, the topmost is "the least specific" one
  (ch. 11, `11_types.md:1721`).

  A call becomes a call of a helper this pass writes for its `B`, before
  types as values are written as classes (`TypeValues.desugar`), so that
  the classes the helper names as values and its result type are theirs:

      $GetCastableFinalSuperClass:B(X:B)<reads><decides>:castable_subtype(B) =
          if (C1[X]) then C1 else if (C2[X]) then C2 else (fail)
      $GetCastableFinalSuperClassFromType:B(T:type)<reads><decides>:castable_subtype(B) =
          if (subtype(C1)[T]) then C1 else … else (fail)

  with the candidates `C1`, `C2`, … topmost first. A cast of a type value
  to `subtype(C)` succeeds when the type it holds is `C` or below it
  (`TypeValues`: `subtype(A)` is below `subtype(P)` for each parent `P`).
  A `B` that is no class or interface (`int`, `any`) has no candidate: its
  helper fails always, and its result is a `type`. No Verse Core is added.
-/
import OpenVerse.Front.TypeValues

namespace OpenVerse.Front.FinalSuper

/-- The functions this pass writes calls of. -/
def instanceName : String := "GetCastableFinalSuperClass"
def fromTypeName : String := "GetCastableFinalSuperClassFromType"

/-- The helper a call of `f` with first argument `b` becomes. -/
def helperName (f b : String) : String := s!"${f}:{b}"

/-- The type names that are no class or interface, which the first
    argument may be (its call then always fails): the built-in types and the
    program's structs and enums. -/
def otherTypeNames (tops : List STop) : List String :=
  builtinTypeNames ++ tops.filterMap fun
    | .const _ n _ none (.structDef ..) | .const _ n _ none (.enumDef ..) => some n
    | _ => none

/-- The calls of the functions `fns` in `e`: where, which, and the first
    argument. -/
partial def calls (fns : List String) (e : SExpr) : List (Pos × String × SExpr) :=
  (match e with
   | .app p (.ident _ f) (b :: _) _ => if fns.contains f then [(p, f, b)] else []
   | _ => []) ++ e.children.flatMap (calls fns)

/-- The program with the calls of the two functions made calls of the
    helpers it adds for them (the file's comment); unchanged when it calls
    neither, or defines a function of either name. -/
def desugar (tops : List STop) : Except String (List STop) := do
  let defines (n : String) : Bool := tops.any fun | .fn _ m .. => m == n | .const _ m .. => m == n | _ => false
  let fns := [instanceName, fromTypeName].filter (!defines ·)
  let all : List (Pos × String × SExpr) := tops.flatMap fun t => t.code.flatMap (calls fns)
  if all.isEmpty then return tops
  -- the classes and interfaces, with their parents as the classes they name
  let classes0 : List (String × List String × List String × Bool) := tops.filterMap fun
    | .classDef _ n _ _ specs parents isI _ _ =>
      some (n, specs, parents.filterMap (fun | .name m => some m | .app m _ => some m | _ => none), isI)
    | _ => none
  let names := classes0.map (·.1)
  -- (a parent as its class's module writes it, `c` or `M.c`, as
  -- `TypeValues.desugar` resolves it)
  let resolve (owner p : String) : String :=
    let p := p.replace "." "::"
    let mods := (owner.splitOn "::").dropLast
    let cands := (List.range (mods.length + 1)).reverse.map fun k => "::".intercalate (mods.take k ++ [p])
    (cands.find? names.contains).getD p
  let classes := classes0.map fun (n, specs, ps, isI) => (n, specs, ps.map (resolve n), isI)
  let parentsOf (n : String) : List String := ((classes.find? (·.1 == n)).map (·.2.2.1)).getD []
  let rec supersOf (fuel : Nat) (n : String) : List String :=
    match fuel with
    | 0 => [n]
    | fuel + 1 => n :: (parentsOf n).flatMap (supersOf fuel)
  let supers (n : String) : List String := (supersOf (classes.length + 1) n).eraseDups
  let specsOf (n : String) : List String := ((classes.find? (·.1 == n)).map (·.2.1)).getD []
  let castable (n : String) : Bool := (supers n).any (specsOf · |>.contains "castable")
  -- (a class some object can have: one at or below it that is no interface
  -- and not abstract; a cast to one no object has is refused)
  let inhabited (c : String) : Bool := classes.any fun (d, specs, _, isI) =>
    !isI && !specs.contains "abstract" && (supers d).contains c
  -- the candidates for `b`: the castable `<final_super>` classes right
  -- below it, topmost first
  let candidates (b : String) : List String :=
    let cs := classes.filterMap fun (c, specs, ps, isI) =>
      if !isI && specs.contains "final_super" && ps.contains b && castable c && inhabited c then some c else none
    (cs.toArray.qsort fun x y => (supers x).length < (supers y).length).toList
  let others := otherTypeNames tops
  -- each call's first argument: a class's or an interface's name, or
  -- another type's; the helpers, one per function and argument
  let mut helpers : List STop := []
  let mut written : List String := []
  for (p, f, b) in all do
    let bn ← match b with
      | .ident _ n => if names.contains n || others.contains n then pure n else
          throw s!"{p.show}: {f}'s first argument is a type written there, the base type, and {n} is no type openverse knows there (a type parameter or a value is not supported)"
      | _ => throw s!"{p.show}: {f}'s first argument is the name of a type written there, the base type (an applied parametric type is not supported)"
    let h := helperName f bn
    if written.contains h then continue
    written := written ++ [h]
    let isClass := names.contains bn
    let p0 : Pos := { line := 0, col := 0 }
    let resTy : STy := if isClass then .app "castable_subtype" [.name bn] else .name "type"
    let fails : SExpr := .block p0 [.decl p0 "$none" (some (.opt resTy)) false (.ident p0 "false"), .query p0 (.ident p0 "$none")]
    let x : String := if f == instanceName then "X" else "T"
    let test (c : String) : SExpr :=
      if f == instanceName then .app p0 (.ident p0 c) [.ident p0 x] true
      else .app p0 (.ident p0 (TypeValues.ifaceName "subtype" c)) [.ident p0 x] true
    let body : SExpr := (if isClass then candidates bn else []).foldr
      (fun c rest => .ite p0 [test c] (.ident p0 c) (some rest)) fails
    let paramTy : STy := if f == instanceName then .name bn else .name "type"
    helpers := helpers ++ [.fn p0 h [{ name := x, ty := paramTy }] [] ["reads", "decides"] resTy body]
  -- the calls, of the helpers, with their other arguments
  let rewrite : SExpr → SExpr := fun
    | e@(.app p (.ident q f) (.ident _ b :: rest) br) =>
      if fns.contains f then .app p (.ident q (helperName f b)) rest br else e
    | e => e
  return helpers ++ tops.map (STop.mapAll id rewrite)

end OpenVerse.Front.FinalSuper
