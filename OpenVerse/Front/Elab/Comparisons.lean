/- How `=` and `<>` compare values of two types (`TyEnv.cmpPlan`, which
   `elabCmp` follows): what their values have in common, where Verse Core's
   equality is Verse's, and the test each plan writes; public declarations
   retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Context

namespace OpenVerse.Front
open OpenVerse

/-- `void` occurs in the type: as it, or inside containers, tuples and type
    arguments. -/
partial def Ty.mentionsVoid : Ty → Bool
  | .void => true
  | .arr t | .opt t => t.mentionsVoid
  | .map k v | .weakMap k v => k.mentionsVoid || v.mentionsVoid
  | .tup ts | .struct _ ts => ts.any Ty.mentionsVoid
  | _ => false

/-- The type with `tuple()`, which takes the empty value alone, for each
    `void`, which takes any value and makes it the empty value. -/
partial def Ty.voidToUnit : Ty → Ty
  | .void => .tup []
  | .arr t => .arr t.voidToUnit
  | .opt t => .opt t.voidToUnit
  | .map k v => .map k.voidToUnit v.voidToUnit
  | .weakMap k v => .weakMap k.voidToUnit v.voidToUnit
  | .tup ts => .tup (ts.map Ty.voidToUnit)
  | .struct n ts => .struct n (ts.map Ty.voidToUnit)
  | t => t

/-- What the values of two types have in common, for `=` between them. -/
inductive Common where
  /-- no value -/
  | nothing
  /-- the empty value only -/
  | empty
  /-- other values too, or values these types do not show -/
  | values
  deriving BEq, Inhabited

/-- What values of `a` and `b` have in common (Book of Verse ch. 4: values of
    different types are different values, "Comparisons between different
    types still compile, but they always fail"; ch. 2: but for the one empty
    value). A value of one type is one of another as the empty value, as an
    int is a rational and a refinement its base, as a tuple is the array of
    its elements, and part by part in options, arrays, maps, tuples and the
    fields of one struct at two instances; classes (references) and type
    parameters do not show their values here. -/
partial def TyEnv.common (env : TyEnv) (a b : Ty) : Common :=
  -- (containers of such parts: the empty one always, others when the parts have values in common)
  let inside (c : Common) : Common := if c == .nothing then .empty else .values
  let parts (cs : List Common) : Common := if cs.contains .nothing then .nothing else .values
  let fieldTys (n : String) (ts : List Ty) : List Ty := (env.fields n ts).map (·.2.1)
  if a == b then .values else
  match a, b with
  | .int, .rational | .rational, .int | .param .., _ | _, .param .. => .values
  | .refine n, t | t, .refine n => match env.refines.lookup n with
    | some (base, _) => env.common base t
    | none => .values
  | .opt x, .opt y | .arr x, .arr y => inside (env.common x y)
  | .map k v, .map k' v' => inside (env.common (.tup [k, v]) (.tup [k', v']))
  | .tup xs, .arr y | .arr y, .tup xs => if xs.isEmpty then .empty else parts (xs.map (env.common · y))
  | .tup xs, .tup ys =>
    if xs.length != ys.length then .nothing else parts ((xs.zip ys).map fun (x, y) => env.common x y)
  | .struct S xs, .struct T ys =>
    if env.classes.contains S || env.classes.contains T then .values
    else if S == T then parts ((fieldTys S xs).zip (fieldTys T ys) |>.map fun (x, y) => env.common x y)
    else .nothing
  | a, b => if a.emptyValue?.isSome && b.emptyValue?.isSome then .empty else .nothing

/-- The type holds one of Verse Core's four empty values (`Value.isEmpty`). -/
def _root_.OpenVerse.VTy.holdsEmpty : VTy → Bool
  | .logic | .opt _ | .arr _ | .tup [] => true
  | _ => false

/-- Verse Core's equality (`Value.veq`) can find a value of one type equal to
    one of the other: equal scalars; the empty values of two types that hold
    one; tuples part by part; type variables and references may. -/
partial def _root_.OpenVerse.VTy.overlaps (a b : VTy) : Bool :=
  (a.holdsEmpty && b.holdsEmpty) || match a, b with
  | .int, .int | .logic, .logic | .char, .char | .float, .float => true
  | .arr _, .arr _ | .opt _, .opt _ => true
  | .tup xs, .tup ys => xs.length == ys.length && (xs.zip ys).all fun (x, y) => x.overlaps y
  | .var _, _ | _, .var _ => true
  | .ref .., .ref .. | .ref .., .vref .. | .vref .., .ref .. | .vref .., .vref .. => true
  | _, _ => false

/-- How `=` and `<>` compare values of two types. -/
inductive CmpPlan where
  /-- Verse Core's equality is Verse's -/
  | core
  /-- no value in common: never equal, though Verse Core could find them so
      (an `int` and a `char32` or an enum, two structs of one layout) -/
  | never
  /-- only the empty value in common, as Verse Core holds it at each, and
      other values Verse Core could find equal (`[]int` and `[]char32`) -/
  | empty (ex ey : Value)
  /-- other values in common that Verse Core holds differently, or could
      not tell from those that are not (`[]tuple(int, []int)` and
      `[]tuple(int, []char32)`, a tuple of type parameters and a string) -/
  | refuse
  /-- both boxed (`boxedTest`): a `comparable` in either type, or values
      Verse Core holds differently -/
  | boxed

/-- Verse Core's equality (`Value.veq`, which relates the empty values) of
    a value of `a` and one of `b` is Verse's: part by part, where the types
    are the same, or what they have in common (`TyEnv.common`) is the empty
    value at most and it finds no other values equal (an `int` and a
    `float`; `logic` and `[]int`; `?logic` and `?void`). Type parameters and
    classes (references) are compared as Verse Core compares them. -/
partial def TyEnv.coreExact (env : TyEnv) (a b : Ty) : Bool :=
  let fieldTys (n : String) (ts : List Ty) : List Ty := (env.fields n ts).map (·.2.1)
  let (va, vb) := (a.toVTy env, b.toVTy env)
  if a == b then true else
  match a, b with
  | .param .., _ | _, .param .. => true
  | .refine n, t | t, .refine n => match env.refines.lookup n with
    | some (base, _) => env.coreExact base t
    | none => false
  | .opt x, .opt y | .arr x, .arr y => env.coreExact x y
  | .map k v, .map k' v' => env.coreExact (.tup [k, v]) (.tup [k', v'])
  | .tup xs, .tup ys => xs.length != ys.length || (xs.zip ys).all fun (x, y) => env.coreExact x y
  | .struct S xs, .struct T ys =>
    if env.classes.contains S || env.classes.contains T then true
    else if S == T then (fieldTys S xs).zip (fieldTys T ys) |>.all fun (x, y) => env.coreExact x y
    else !va.overlaps vb
  | _, _ => match env.common a b with
    | .nothing => !va.overlaps vb
    -- (Verse Core's equality relates the empty values; no other values
    -- could be equal: an array and a map of parts that no two Verse Core
    -- values of the two types are equal in)
    | .empty => match va, vb with
      | .arr x, .arr y | .opt x, .opt y => !x.overlaps y
      | _, _ => true
    | .values => false

/-- Converting a value of `a` to `b` keeps any two values apart that were
    apart: no part becomes `void` or `any`, which make every value one, so a
    comparison may convert an operand to the other's type
    (`(1, 2) = array{(), ()}` must not hold). -/
partial def TyEnv.lossless (env : TyEnv) (a b : Ty) : Bool :=
  if a == b then true else
  match a, b with
  | _, .void | _, .any => false
  | .int, .rational | .never, _ => true
  | .refine n, t => match env.refines.lookup n with
    | some (base, _) => env.lossless base t
    | none => false
  | .arr x, .arr y | .opt x, .opt y => env.lossless x y
  | .map k v, .map k' v' => env.lossless k k' && env.lossless v v'
  | .tup xs, .tup ys => xs.length == ys.length && (xs.zip ys).all fun (x, y) => env.lossless x y
  | .tup xs, .arr y => xs.all (env.lossless · y)
  | .struct S xs, .struct T ys =>
    if env.classes.contains S && env.classes.contains T then true
    else S == T && (((env.fields S xs).map (·.2.1)).zip ((env.fields T ys).map (·.2.1))).all
      fun (x, y) => env.lossless x y
  | _, _ => false

/-- How `=` and `<>` compare a value of `a` with one of `b`, different
    types: by Verse Core's equality where that is Verse's
    (`TyEnv.coreExact`), else by what they have in common (`TyEnv.common`):
    nothing, never equal; the empty value only, equal when both are empty;
    other values, refused. -/
def TyEnv.cmpPlan (env : TyEnv) (a b : Ty) : CmpPlan :=
  if env.coreExact a b then .core else
  match env.common a b, a.emptyValue?, b.emptyValue? with
  | .nothing, _, _ => .never
  | .empty, some ea, some eb => .empty ea eb
  | _, _, _ => .refuse

/-- `x op y` (`=` or `<>`) of the slots `x` and `y`, of types that have the
    empty value only in common, which Verse Core holds as `ex` and `ey`:
    `x = y` when both are empty, `x <> y` when either is not. -/
def emptyTest (op : Prim) (x : Nat) (ex : Value) (y : Nat) (ey : Value) : Expr :=
  if op == .eq then .seq (p2 .eq (.local y) (.lit ey)) (p2 .eq (.local x) (.lit ex))
  else .ite (p2 .eq (.local y) (.lit ey)) (p2 .ne (.local x) (.lit ex)) (.local x)

/-- `x op y` (`=` or `<>`) of the slots `x` and `y` of types with no value in
    common: `=` fails and `<>` holds, as `0 op 1` does, `x` its value. -/
def neverTest (op : Prim) (x : Nat) : Expr :=
  .seq (p2 op (.lit (.int 0)) (.lit (.int 1))) (.local x)

/-- `x op y` by the plan, given the slots of `x` and `y`. -/
def CmpPlan.test : CmpPlan → Prim → Nat → Nat → Expr
  | .never, op, x, _ => neverTest op x
  | .empty ex ey, op, x, y => emptyTest op x ex y ey
  | _, op, x, y => p2 op (.local x) (.local y)

end OpenVerse.Front
