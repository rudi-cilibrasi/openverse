# Variance of parametric classes: what Verse Core needs

A design, left for the owner's go-ahead: it changes Verse Core's typing
(`OpenVerse/Core/`) and the statements of its theorems. Nothing here is
built. It is the cause of 38 refusals of the Book test survey (variance),
of 34 more whose shared definitions need it (archetype-blocks, all in
`ParametricTypes.versetest`), and of 8 joins (`SOL-6739-ParametricTypeMeetAndJoin`,
under subtyping-to-any): [book-test-conformance.md](book-test-conformance.md),
"Classes and subtyping: the map".

## The Book's rule

Ch. 10, "Instantiation and Identity" (`10_classes_interfaces.md:1300-1490`):

- "While different instantiations of a parametric class are distinct
  types, Verse allows certain instantiations to be used in place of others
  based on **variance**." (`:1306-1309`)
- "The variance of a parametric type depends on how the type parameter is
  used within the class definition." (`:1312-1313`)
- Covariant: "When a type parameter appears only in **return positions**
  (method return types, field types being read), the parametric class is
  **covariant** in that parameter" (`:1328-1331`): `producer(player)` is a
  `producer(entity)`.
- Contravariant: "only in **parameter positions** (method parameters being
  consumed)" (`:1361-1364`): `consumer(entity)` is a `consumer(player)`.
- Invariant: "in both parameter and return positions" (`:1394-1396`).
- Bivariant: "not used in any member signature, neither in the type's own
  members nor in any member it inherits" (`:1437-1439`): any instantiation
  is any other.
- "Variance is computed over a type's full member set, including members
  inherited from a parametric base." (`:1467-1468`)

The tests (`ParametricTypes.versetest` 56-177, 486-560, 929-1225) check
each kind for classes and interfaces, directly and through a class below
(`bivariant_sub_class(t) := class(bivariant_class(t))`), with function
fields and methods, and the joins of `SOL-6739`. A `var` field is read and
written, so it makes its parameter invariant (the soundness argument below
needs it; the tests' `var` fields are of other types).

The prose and the tests agree.

## What Verse Core does

A class or interface `T(args)` is `VTy.ref ts args` (DESIGN.md, "Classes
as references"), and:

- **Subtyping** (`VTy.sub`, `Core/Typing.lean:241`):
  `.ref ts as ≤ .ref us bs` exactly when `ts ⊆ us` and `bs` is a prefix of
  `as`: the type arguments of the target are those of the source, equal
  position by position. A view (`vref`, #351) relates a class's arguments
  to an interface's by an equality (`bs.isPrefixOf (e.2.map (inst as))`).
- **Values** (`hasTy`, `:278`): `hasTy Ξ (.ref a) (.ref ts args)` holds
  when the object `a` has, in the heap typing `Ξ` (`HeapTy`), a class in
  `ts` and type arguments of which `args` is a prefix: exactly them.
- **Fields** (`FieldTy`, `:434`): field `k` has the one type `f.inst args`
  in every class of `ts`; `heap_get` and `heap_set` (`:466-469`) read and
  write it at that type.
- **Heap** (`HeapOK`, `:596`): every object's fields have its class's
  field types at its own type arguments.

So a `producer(player)` object (`Ξ[a] = (producer, [player])`) is not a
value of `.ref [producer] [entity]`, and no `Typed.sub` step can make it
one.

## Why the front end cannot do it alone

- *A conversion* at the use (`X:producer(entity) = PlayerProducer`) would
  have to make a new object: a class value is a reference, and the object's
  identity is observable (its `var` fields, `<unique>` equality), so a copy
  is not the same value.
- *A view* (#351) relates type arguments by equalities only.
- *Another representation*: holding a covariant parameter's values boxed in
  `dyn` (`ref ts [dyn]`) would change the layout and code of every
  parametric class with such a parameter, so the bytes of every program
  that has one, and a read would need an unboxing that cannot fail, which
  Verse Core does not have.

## Design

**Variances in the certificate.** `Sigs` gains, for each class, the
variance of each of its Verse Core type arguments, `variances : List (List
Variance)` with `Variance := co | contra | inv | bi`, and for each field
whether it is a `var` (the class table has its types only). The checker
(`Prog.checkTypes`) checks them against the class table: a variable in a
`var` field is `inv`; in a field type, each occurrence's polarity
(arrays, options, tuples and maps' values covariant; a function type's
parameters contravariant and result covariant; a reference's arguments by
that class's variances); the variance of a class is at most that of each
class or interface it is below (its members include the inherited ones,
ch. 10 `:1467`); a method's parameter types count contravariantly and
its result covariantly. The front end computes them the same way, from
the source, and writes them (`TyEnv`, `Elab/Environment.lean`).

**Subtyping and values over the variances.** `VTy.sub` and `hasTy` take
the variances (`S.variances`, or the certificate):

- `.ref ts as ≤ .ref us bs` when `ts ⊆ us` and, for `i < bs.length`,
  `as[i] ≤ bs[i]` where every class of `ts` is `co` at `i`, `bs[i] ≤
  as[i]` where `contra`, anything where `bi`, `as[i] = bs[i]` otherwise
  (a prefix still: more arguments below fewer);
- `hasTy Ξ (.ref a) (.ref ts args)` when `Ξ[a] = (t, args')`, `t ∈ ts` and
  `args'` relates to `args` as above by `t`'s variances.

The soundness argument is the usual one: a field read through
`.ref ts args` gives `f.inst args`, and the object's field has
`f.inst args'`; where the class is `co` at `i`, the variable occurs in `f`
only covariantly, so `f.inst args' ≤ f.inst args` (a lemma, monotonicity of
`inst` in the polarity of the occurrence); a `var` field mentions only
`inv` variables, so `heap_set` writes at the object's own type; a method
generic over the class's parameters is typed once and called at the
reference's arguments (`dispatch`), which needs the same lemma for its
`Self` parameter.

**Joins.** `VTy.join` (`Core/TypeCheck.lean:124`) of two references of one
class at different arguments joins position by position by variance
(`SOL-6739`); the front end's `joinTy` the same.

**What does not change.** OVBC carries no types (FORMAT.md): the encoder,
`openverse.h` and `load.c` are unchanged, and the C runtime erases types.
Programs that compile today keep their bytes: their conversions are at
equal arguments.

## Theorems whose statements change

`hasTy` and `VTy.sub` gain a parameter (the variances), so every statement
that mentions them changes, though not its meaning for programs without
variance:

- `Core/Typing.lean`: `VTy.sub`, `VTy.subL`, `hasTy`, `allTy`, `allTys`,
  `sub_dyn`, `dyn_sub_iff`, `HeapOK`, `FieldTy` (unchanged in form; its
  use in `heap_set` gains the `var`/`inv` premise through the checker).
- `Core/TypeSafety.lean`: `allTy_iff`, `allTys_*`, `allTy_*`,
  `hasTy_subst`, `allTys_subst`, `FieldTy.subst`, `VTy.sub_vref_iff`,
  `VTy.sub_ref_vref_iff`, `hasTy_vref_iff`, `VTy.sub_refl`,
  `VTy.subL_refl`, `VTy.sub_trans`, `VTy.subL_trans`, `VTy.sub_subst`,
  `VTy.subL_subst`, `hasTy_sub`, `allTys_sub`, `ResOK_sub`,
  `Typed.subst`, `TypedL.subst`, `hasTy_mono`, `hasTy_ref`, `ref_arg`,
  `ref_pins`, `ref_open`, `vref_pins`, `vref_open`, `HeapOK.new` and the
  preservation lemmas that use them; a new lemma, `inst` monotone by
  polarity.
- `Core/TypeCheck.lean`: `VTy.join`, `VTy.join_sub`, `VTy.joinL_sub`, the
  checker's soundness.
- `Core/Guarantees.lean`: `Prog.accepted` (its `hasTy` in the conclusion).
- `Core/Check.lean`: the certificate check gains the variance check.

## Size and order

80 cases of the survey (38 + 34 + 8). The proofs are the largest part: every
lemma about references and `hasTy` above, by the same structure, with the
variance cases added. A smaller first step is bivariance alone (a position
that no field or method mentions is free, `hasTy` ignores it): it changes
the same statements but needs no polarity lemma; it gives the bivariant
cases (about a third).

## Review, before building

The Book's rule is read right above, and the polarity lemma is the right
lemma for field reads. Three things the design leaves out make it unsound as
written, and one makes it bigger than it needs to be.

**Which variance a reference has.** In Verse Core a reference type is a set
of *concrete* classes, `ref ts args` (no interface and no abstract class has a
tag), and Verse Core lets code read every field the classes of `ts` share
(`FieldTy`) and call every method of theirs as a generic function at the
reference's own arguments (`Typed.call`, `Typed.dispatch`). So the variance
that makes a value of `ref ts args` sound is that of the *object's own
class*, computed from its own field table, not the variance of the source
type the reference stands for. The Book types an override at the object's
own arguments and converts at the call through the declared signature;
Verse Core has no such rule. A counterexample to taking the source type's
variance (the design's "`S.variances` ... the variance of a class is at most
that of each class or interface it is below" leaves this open):

```verse
c(t:type) := class<abstract>:
    M(X:t):void                       # contravariant in t (Book)
impl(t:type) := class(c(t)):
    D:t                               # covariant in t: impl is invariant
    M<override>(X:t):void = ...       # reads D at the receiver's t
X:c(int) = impl(comparable){D := 2.0} # Book: valid, c is contravariant
X.M(1)                                # Verse Core: impl.M called at t = int,
                                      # reads D, a float, as an int
```

With `ref [impl] [int]` holding an `impl` made at `comparable`, `FieldTy`
types `D` as `int` and `Typed.subst` types `impl.M`'s body at `int`:
preservation fails at the read. So a conversion `C(a) ≤ C(b)` must hold in
the variance of every concrete class below `C` too: openverse refuses
`SOL-6739`'s contravariant `contravariant_class_impl(comparable)` as a
`contravariant_class(int)` (its `Data:t`), which the Book accepts.

**Verse Core has no contravariant position.** Its types are first order:
arrays, options, tuples and references (function values are objects of
classes, `FnValues`). A type variable in a field type is used positively,
under an invariant position, or not at all. So a class's variance in Verse
Core is `co`, `inv` or `bi`; the Book's contravariance (method parameters,
function-typed fields) is Verse Core bivariance when no concrete class holds
the parameter in a field. (A function-typed field holds an object of a
function value class, which fixes the shape's type arguments: invariant.)
The `contra` case and the polarity flip of the design are not needed in
Verse Core; the front end has them, over source types.

**Pins.** A class that fixes or repeats a type argument (#142, #209:
`intcell := class(cell(int))`) has its dispatch, and a refining cast to it
(#243), typed under an *equational* refinement of the receiver's arguments
(`Typed.dispatch`, `PinRefines`); `ref_open` proves it sound because the
object's arguments extend the receiver's. Under covariance they do not: the
object's argument is below the receiver's. Counterexample:

```verse
cell(t:type) := class{V:t}            # covariant
pcell := class(cell(player)){}        # fixes t: pinned when cast to
box(t:type) := class{var B:t}         # invariant
F(C:cell(t), Bx:box(t) where t:type):void =
    if (P := pcell[C]):               # lifted at t := player (#243)
        X:player = Bx.B               # Bx is a box(entity) at run time
        Print(X.Name)                 # an entity has no Name
F(cell(entity) := pcell{V := player{...}}, box(entity){B := entity{}})
```

The lifted branch takes `Bx` at `box(player)`; at run time `t = entity`, so
the read gives an `entity` typed `player`, and the field read after it is a
Verse Core type error. So a class's pins may mention only its invariant
positions: a pinned position, and every position a pin mentions, is
invariant (a well-formedness condition the checker decides). Then
`ref_open` still holds: with `X` the object's arguments and `a` the
reference's, `a ++ X.drop a.length` agrees with the pins exactly where `X`
does, and the object is a value of `ref us (a ++ …)` by its variance.

**Writes.** `heap_set` writes at the reference's arguments, so it needs the
field to mention only invariant positions of each class of the reference;
the design's per-field `var` flags would miss the compiler's own writes (the
accessors' `$set`, #157, generated for fields that are no `var`). A premise
of `Typed.heap_set` covers every write, needs no flag, and makes a `var`
field (also one a subclass adds) invariant for its class by the check.

**Casts and the runtime.** `isTag us` tests the tag only, and its result
keeps the reference's arguments (`Typed.heap_isTag`); with the object's own
variance in `hasTy`, that is sound unchanged. A cast `C(entity)[X]` of an
object made as `C(player)` succeeds in openverse when the cast's classes are
covariant there, as the Book has it (the object is a `C(entity)`). The C
runtime never sees type arguments (`isTag` compares tags), so nothing in it
changes. Casts to parametric types at other arguments are a compile error
in the Book (ch. 10 "cannot cast to parametric type", 3502).

**Views** (`vref`, #351) stay invariant: a reference through views relates
the view's arguments to the object's by an equation. A class reference fits
a view only where the view mentions invariant positions of the class.

**Joins.** Verse Core has no meet and needs none: a join is checked at an
expected type where there is one (the front end gives it), and in infer
mode `VTy.join` joins covariant positions and takes either argument at a
bivariant one. The front end's join is the Book's (contravariant positions
meet, at an expected type).

**Bivariance first?** Not as a separate step: it needs the same changes to
`hasTy` and `sub` and the same well-formedness for pins and writes; only the
polarity lemma is smaller.

**Recursive uses.** The Book's tests do not decide whether `c(t) :=
class{Next:?c(t)}` is bivariant ("not used in any member signature", ch. 10,
or used, at a position of its own class). The fixpoint that gives each
class the most permissive variance consistent with its members (start at
`bi`, raise until stable) says bivariant; it is sound (the checker checks
the result, whatever it is), and no test of the Book contradicts it.
