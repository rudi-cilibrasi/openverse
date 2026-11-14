# Variance of parametric classes and interfaces

Built: Verse Core's typing of references by the classes' variances, with
every proof closed (`OpenVerse/Core/`), the certificate checker, and the
front end's variance by the Book's rule. It was the cause of 38 refusals of
the Book test survey (variance), of 31 more whose shared definitions need it
(archetype-blocks, all in `ParametricTypes.versetest`), and of 8 joins and 8
conversions of `SOL-6739-ParametricTypeMeetAndJoin`:
[book-test-conformance.md](book-test-conformance.md), "Variance". The
sections below are the Book's rule, the design proposed before building,
its review (three counterexamples), the design as built, where openverse
still refuses what the Book accepts, and what is left.

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
written, so it makes its parameter invariant (ch. 6, "Polarity and
Variance": "`c(t:type) := class{var X:t}` # Mutable field makes c invariant
in t"; the tests' `var` fields are of other types, and two variance tests
with `var` fields are commented out, "classes containing pointer members
aren't allowed").

The prose and the tests agree.

## What Verse Core did

Before this work, a class or interface `T(args)` was `VTy.ref ts args`
(DESIGN.md, "Classes as references"), and (lines of `Core/Typing.lean` at
`215af57`):

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

## The design proposed

The proposal before building: `Sigs` gains each class's variances
(`co | contra | inv | bi`) and each field's `var` flag; the checker checks
the variances against the class table (fields, function-typed fields'
flips, `var` fields invariant, a class's variance at most that of each
class or interface above it); `VTy.sub` and `hasTy` relate references'
type arguments by the variances; the soundness argument is a lemma, `inst`
monotone in the polarity of the occurrence, for field reads, and the same
for a method's `Self` at a dispatch; `VTy.join` joins by variance; OVBC and
the C runtime are unchanged. A smaller first step was bivariance alone.

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

## The design as built

**Verse Core** (`Core/Typing.lean`, `Core/TypeSafety.lean`):

- `Variance := inv | co | bi`, and `Sigs.variances : List (List Variance)`,
  each class's at each of its Verse Core type arguments, `inv` past the
  list (`Sigs.var`). No `contra`: Verse Core's types have no contravariant
  position (above).
- `VTy.sub V`: `.ref ts as ≤ .ref us bs` when `ts ⊆ us` and `as` fit `bs`
  for every class of `ts` (`VTy.subArgs`): `bs` no longer, and at each of
  its positions `i`, for each `t ∈ ts`, `as[i] = bs[i]` where `V t i = inv`,
  `as[i] ≤ bs[i]` where `co`, any where `bi`. A class's reference fits a
  view only where the view mentions the class's invariant arguments.
- `hasTy V Ξ (.ref a) (.ref ts args)`: `Ξ[a] = (t, X)`, `t ∈ ts`, and `X`
  fits `args` for `t` alone (`VTy.subArgs V [t] 0 X args`): an object has
  the reference types its own class's variances give it.
- `Sigs.VarOK` (in `Sigs.Closed`, so in `ProgTyped`): each class's field
  types use its arguments as its variances say (`VTy.posIn`: a variable
  only where its variance is `co` or `inv`, inside a reference's argument
  covariantly where the reference's classes are covariant there, and only
  invariant variables where any is invariant, or in a view), and its pins
  pin and mention only invariant arguments.
- `Typed.heap_set` takes `FieldSet S ts k`: field `k` of each class of `ts`
  mentions only its invariant arguments.
- The lemmas: `VTy.sub_refl`, `VTy.sub_trans`, `VTy.sub_subst` and
  `hasTy_sub` by the same structure, with `VTy.subArgs_*`; **the polarity
  lemma**,

  ```lean
  theorem VTy.posIn_sub {V : Variances} {W : Nat → Variance} {σ σ' : Nat → VTy} {n : Nat}
      (hσ : ∀ j < n, (W j).Rel V (σ j) (σ' j)) :
      ∀ f : VTy, f.posIn V W = true → f.varsBelow n = true → (f.subst σ).sub V (f.subst σ') = true
  ```

  and at an object, `VTy.inst_sub_of_fit` (a field read at a reference's
  arguments gives a value of the field's type there) and
  `VTy.inst_eq_of_fit` (a field of invariant variables is the same type at
  both: a write). `ref_pins` and `ref_open` take `S.VarOK`: the reference's
  arguments followed by the rest of the object's agree with its pins, as
  those mention only invariant arguments, where the object's are the
  reference's; so `Typed.dispatch`'s refinement stays sound unchanged.
- Before variance as a special case: `hasTy_allInv_ref` (with every class
  invariant, a reference has a reference type exactly when its arguments
  extend the type's), `VTy.sub_ref_of_prefix` (every subtyping between
  references that held before holds at every variances),
  `Sigs.checkVarOK_nil`, `fieldSet_nil` (a certificate without variances
  passes the new checks wherever the old checker read a field).

**The checker** (`Core/TypeCheck.lean`): `Sigs.checkVarOK` (sound for
`Sigs.VarOK`) in `Prog.checkTypes`; `fieldSet` at each `set`; `expect`,
`litTy`, the dispatch checks and `checkDefault` at `S.var`; `VTy.join V`
joins references at arguments both fit (`VTy.joinArgs`: equal ones, a
covariant position's join, a bivariant position's first), proved
(`VTy.join_sub`, `VTy.joinArgs_sub`).

**The front end**: two variances, each of its language.

- The Book's, over source types (`Front/Variance.lean`,
  `TyEnv.bookVariances`): each type parameter of a class or interface by its
  uses in the fields (a `var` one invariant), the methods (parameters
  contravariant, results covariant: each overload's) and the parents at
  the arguments it gives them, through nested types (arrays, options,
  tuples and maps covariant, a class's arguments by its variance, a
  function type's parameters contravariant and its result covariant); the
  most permissive solution, from `bi` up to a fixpoint. A function type's
  own shape is invariant at conversions (`TyEnv.varianceOf`): function
  values convert by adapters (#214), as before.
- Verse Core's (`TyEnv.coreVariancesOf`, by `Sigs.inferVariances` in Core):
  over the class table, each argument a pin pins or mentions, a field
  written through a reference mentions (a `var` field, inherited ones and a
  placeholder's too, or one with an accessor pair, #157), or a view of an
  interface above mentions, invariant; the rest from the fields; from `bi`
  up to a fixpoint. The certificate gives it; the checker checks it.
- A conversion of a class's instance to one above (`refUp`): the Book's
  variance of the class above relates the arguments (each a value of the
  other as it is: a class below, a refinement of it, `comparable` for a
  value that is its own box; `TyEnv.argFits`), *and* Verse Core's subtyping
  of the two references holds, by the same `VTy.sub` the checker uses, as
  no value changes. So no conversion the front end makes can fail the
  checker. An instance of a class with no object below it converts by the
  Book's rule alone (its Verse Core type is the empty tuple at every
  argument).
- Joins (`joinTyShaped`): at an expected type, both branches convert to it;
  without one, a class above both at arguments by its variance (the join
  where covariant, the lower where contravariant, either where bivariant).
- Messages (`TyEnv.varianceWhy`): the Book's verdict (the variance and the
  members that make it), or the class below and the Verse Core reason (a
  field holding or written at the parameter, a pin, a view).
- An empty archetype block (`X := c(args):` with nothing below), which the
  Book's `ParametricTypes.versetest` writes, parses as `c(args){}`.

**The format and the C runtime**: unchanged. OVBC carries no types, the
certificate lives in the compiler, and a cast compares tags only
(`runtime/src/interp.c`, `tag_in`), so an object made at `C(player)` is a `C(entity)` there by
covariance as in Lean: no seam, no behaviour of C changes.

## Where openverse refuses what the Book accepts

Each refusal says why. All follow from typing a reference by its object's
own class (above):

- a contravariant (or bivariant) conversion of a type with a concrete class
  below it that holds the parameter in a field: `SOL-6739`'s
  `contravariant_class_impl(t)` with `Data:t` (4 cases);
- a conversion to an instance at `any` (`covariant_class(any)`): `any`
  holds no value in openverse, so `int` is no `any` as it is (2 cases;
  `subtyping-to-any`);
- a conversion of a type with a class below that writes the parameter
  (adds a `var` field of it), fixes it and overrides a method or is the
  target of a refining cast (its pins), or sees it through a view (#351);
- a type argument inferred through a variant position: a generic call
  takes it from its first argument (`F(C:box(t), X:t)` at a
  `box(player)` and an `entity`).

Function types keep openverse's adapters (#214): `type{_(:entity):int}` is
a `type{_(:player):int}` where a closed type is written, not by subtyping
of the shapes.

## The survey

See [book-test-conformance.md](book-test-conformance.md), "Variance": the
counts before and after, per cause.

## What is left

- *A declared signature for overrides* in Verse Core: an override typed at
  its object's own type arguments and called through the declared
  signature, with the polarity lemma on the signature. Then a concrete
  class's fields would constrain only its own type, not the types above
  it, and the four `SOL-6739` contravariant cases, the pinned and written
  cases above would convert. It needs `Typed.dispatch`'s refinement to
  become an inequation at variant positions (or the declared signature to
  replace it), and a reference type that knows its view, so that a field
  read through a contravariant view is refused.
- Type argument inference through a variant position.
- `any` as a value-holding top type.
