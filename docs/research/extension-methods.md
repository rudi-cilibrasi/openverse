# Extension methods

An extension method adds a method to a type without changing the type's
definition: `(Value:int).Double()<computes>:int = Value * 2`, called
`X.Double()` or `7.Double()`. This note pins the rules from the Book of
Verse at
[`beaa719`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0)
(chapter 6, "Extension Methods", `docs/06_functions.md:501-756`; chapter
16; its Runtime API reference `docs/api/verse_runtime_api.html`) and from
the Book's own tests, says which readings openverse takes where the Book is
silent, and states the design. No Epic source code was read; the tests are
quoted by file and line only. Case counts are those of
[the survey](book-test-conformance.md).

## The rules

### The definition

- **Form.** "Extension methods use a special syntax where the extended
  type appears in parentheses before the method name" (ch. 6:516-517):
  `(Value:int).Double()<computes>:int = Value * 2` (ch. 6:523). The
  method's own specifiers follow its name, `(S:string).Shout<public>():string`
  (ch. 6:709), and its parameters, effects, result type and body are a
  function's. The tests also write the body after `:=`
  (`Bugs/SOL-3515-CallingExtensionMethodWithoutSelf.versetest:9`,
  `(MyInstance:my_class).DoSomething():int := 40 + MyInstance.X`), as a
  function's may be.
- **The receiver is one parameter.** "When extending tuples, you must
  specify the tuple type explicitly (e.g., `(Point:tuple(int, int))`). You
  cannot use destructured parameter syntax (e.g., `(X:int, Y:int)`) for
  extension method contexts" (ch. 6:560-563). The tests refuse
  `(A:int, B:int).Method()` and `().ExtensionX()` ("These short forms aren't
  valid in ShipVerse for now", `ExtensionFields.versetest:8, 55-58, 79-82`,
  error 3101). The receiver may be unnamed, `(:without_Q).Q():int=11`
  (`ExtensionFields.versetest:170`), as any parameter may.
- **No extension fields.** `(I:int).Member:int=I` and `int.Member:int=22`
  are refused ("Don't allow extension data members",
  `ExtensionFields.versetest:10-13`, error 3502).
- **The receiver's type.** "The type in parentheses can be any Verse type:
  primitives, tuples, classes, interfaces, arrays, maps, or structs"
  (ch. 6:533-534); the chapter extends `int`, `string`, `logic`,
  `tuple(int, int)`, `tuple()` ("The empty tuple `tuple()` represents the
  unit type and can have extension methods", ch. 6:565-566), `[]int`,
  `[int]string` and classes (ch. 6:536-617). A type parameter declared
  inside the receiver's parentheses is a generic receiver:
  `(Input:[int]u where u:type).RemoveKey<public>(KeyToRemove:int)`
  (`Bugs/2023-02-08-MapMemoryLeak.versetest:4`),
  `(S:signalable(t) where t:type).SignalNextTick(Value:t)`
  (`Bugs/FORT-1126351-GenericSignalableDeferredSignalConvertCrash.versetest:39`),
  and the API reference's `(InInstance:t where t:castable_subtype(any)).IsOfType`.
  Options are not shown, but are "any Verse type".
- **Parameters.** "Extension methods support all parameter features
  including named and default parameters" (ch. 6:620-621:
  `(Text:string).Wrap(Open:string, ?Close:string = ">")`). "When an
  extension method has multiple parameters, you can pass a tuple to provide
  all arguments at once" (ch. 6:739-756: `Origin.Translate(Delta)` with
  `Delta := (5, 10)`; also `ExtensionFields.versetest:182-209` and
  `NestedNamedTupleParameters.versetest:49-96`, which give the extension
  methods the same nested tuple parameters as functions).
- **Effects** are a function's: `<computes>`, `<decides>` (called with
  `[]`: `42.IsEven[]`, `"Hello".FirstChar[] = 'H'`, ch. 6:541-545),
  `<reads>` ("Note: Sqrt is <reads>", ch. 6:553), `<transacts>`,
  `<allocates>` (ch. 6:747).
- **Where.** At the top level, in a module (`Utils := module:` with
  `(S:string).Shout<public>()`, ch. 6:708-709), and in a class: "Extension
  methods can be defined inside classes and access class members … This
  creates a lexical closure where the extension method can reference the
  enclosing class's members" (ch. 6:718-737, `game_manager`'s
  `(Score:int).ScaledScore()` reads its `Multiplier`; also
  `ExtensionFields.versetest:143-153`).

### The call

- **Dot notation**, on any expression, literals included: `X.Double()`,
  `7.Double() = 14` (ch. 6:525-530), `(3, 4).Distance()`, `().GetMagicNumber()`,
  `array{1, 2, 3, 4, 5}.Sum()`, `map{1=>"a", …}.Keys()` (ch. 6:557-605),
  `(2).Extension()`, a `var` (`MyVar.IntExtension()`, "failed in an
  earlier version", `ExtensionFields.versetest:34-35`).
- **Overloading.** "You can define multiple extension methods with the same
  name for different types … The compiler selects the appropriate overload
  based on the receiver type" (ch. 6:633-649). Overloads that a call could
  not tell apart are refused: `(A:[]int).AddScalar(B:int)` beside
  `(A:[int]int).AddScalar(B:int)` ("map and array are not distinct",
  `ExtensionFields.versetest:137-141`, error 3532).
- **Not values.** "Extension methods must be called: they cannot be
  referenced as first-class values without calling them" (ch. 6:653-671,
  `F := 5.Double` is an error; `ExtensionFields.versetest:60-63`, error
  3506).
- **Methods of the type come first, and may not be repeated.** "Extension
  methods cannot have the same signature as methods defined directly in
  classes or interfaces … This prevents ambiguity and ensures that class
  methods always take precedence" (ch. 6:673-691; error 3532, also for an
  interface's method and with a parameter, `ExtensionFields.versetest:84-103`).
  A class's method and an extension method from elsewhere that a call fits
  both are ambiguous: an extension `(C:c).ErrorMethodExtra(E:int)` and a
  subclass `b`'s own `ErrorMethodExtra(E:int)`, both open where
  `b{Value:=1}.ErrorMethodExtra(100)` is called (`ExtensionFields.versetest:106-124`,
  error 3518). So the type's members and the extension methods in scope are
  candidates of one call, and two that fit are an error, as two overloads
  are. A field and an extension method of one name on different types do
  not meet: `with_Q{}.Q = 10` is the field, `without_Q{}.Q() = 11` the
  extension method, and the same for a field `Length` and an extension
  `Length()` (`ExtensionFields.versetest:167-179`, "There is some special
  code for Length, check that it doesn't break this example").
- **Scope.** "Extension methods are scoped like regular functions. They are
  only visible where they are defined or imported" (ch. 6:693-715: a
  `<public>` one of a module, after `using { Utils }`). Without the `using`
  the call is refused (`Bugs/FORT-559416-AddExtensionMethodsToForgotUsingMessage.versetest:5`,
  3506), and an overload in a submodule that is not opened is not a
  candidate (`OutOfScopeOverloads.versetest:23-38`, 3509).
- **Without a receiver.** In a method of a class below the receiver's type,
  `DoSomething()` calls the extension method with `Self`, as
  `Self.DoSomething()` does, and a function `DoSomething2():int` of the same
  name makes that call ambiguous (`Bugs/SOL-3515-CallingExtensionMethodWithoutSelf.versetest:7-33`,
  3518).
- **Static.** The API reference calls a method declared in "the
  extension-method form" "non-virtual": "a user-written subclass … must not
  be able to intercept the call" (`log.Print`). An extension method is chosen
  by the receiver's static type and overridden by nothing. The Book says
  nothing of `<override>` on one.
- **Qualified.** "If your module defines `Last` and the array extension
  `Last` is also in scope, `MyModule.Last(X)` becomes ambiguous and must be
  written `MyModule.(MyModule:)Last(X)`" (ch. 16:577-580); the tests
  qualify a definition and a call by a path,
  `(InPlayer:player).(/Verse.org/VerseTests/MyModule:)DoSomething<public>(X:int)`
  and `Player.(/Verse.org/VerseTests/MyModule:)DoSomething(10)`
  (`Bugs/SOL-8768-QualificationOfExtensionFields.versetest:9, 21`).
- **How Verse represents one.** "Mechanically the receiver arrives as the
  first parameter and the call's own empty argument tuple as the second,
  which is why the intrinsic is a two-parameter function. That is how
  extension methods are represented, not something you write" (the API
  reference, `ToCodePoint`). The tests' `operator'.Field'` and
  `operator'.Method'` (`ExtensionFields.versetest:18-25`), which may be
  neither defined nor called, are that function's name.
- **Release.** Chapter 6 marks nested functions "Unreleased Feature"
  (ch. 6:1077) and extension methods not; the Runtime API reference, which
  says it is generated from the Verse runtime, declares library methods in
  this form (`(Byte:char).ToCodeUnit()`, `(Value:int).ToChar()`,
  `(InitialRotation:rotation).ApplyPitch<native><public>(…)`, the `entity`
  methods), and none of the tests above is marked for one VM.

## The design

openverse already has functions with overloading by parameter types (#74,
#106), method calls with static resolution and dynamic dispatch, `(M:)F`
qualification, modules that resolve every name before elaboration, and
built-in methods on types that are no classes (`.Length`, the array
methods, the conversions of chars). The simplest reading that is true to
the rules above, stated before it was built and built as stated:

> An extension method `(R:t).M(…)` is the function `$ext:M(R:t, …)`: an
> ordinary function whose first parameter is the receiver, under a name no
> program can write. A call `X.M(…)` whose name an extension method in
> scope has is the call `$ext:M(X, …)`, unless `X`'s type has a member `M`
> of its own that the call fits.

(The name was first `.M`; a function whose name has a `.` is a method's,
`c.M`, in the elaborator, so `$ext:`, the prefix of the compiler's names,
is its mark. Messages show `M`.)

**What is reused.** Everything a function has: overloads, told apart by the
receiver's type and the parameters', and the check that a call could not
fit two; generic receivers and parameters (a `where` inside the receiver's
parentheses joins the function's type parameters); named parameters and
defaults; effects, `<decides>` and the `[]` it needs; a tuple argument
spread over the parameters after the receiver, as a method's arguments are
(`Sig.hasReceiver`); bodies with several values, which the choice inliner
takes as it takes any function's; `spawn` and `<suspends>`. The receiver is
evaluated once, before the arguments, as a method's receiver is.

**What is added.** The definition head (`parseExtensionHead?`, the
receiver group before the name); in `Front/Modules.lean`, the lookup of
`$ext:M` for a call `X.M(…)` (`Resolver.ext`) and, in a method, for a bare
call (`Resolver.selfExt`); in the elaborator, `elabExtensionCallWith` (the
receiver once, the type's own member or the extension method, ambiguity),
`Ctx.hasOwnMember` (the members a type has: fields, methods, the built-in
methods, which now share one list, `arrayMethods`), the check that an
extension method does not repeat a method of its class (`checkSignatures`)
and the refusal of `X.M` as a value. Nothing is deleted; Verse Core, the
proofs, OVBC and the runtime are unchanged, and a program without an
extension method is elaborated exactly as before (the modules' pass takes
its early way out for it).

**Scope** is the modules': a method call's name is looked up as `$ext:M`,
from the call's scope outward and among the modules its scope opens, as a
function's name is; a call that finds one becomes the function call there,
before the choice inliner and the function values see it. An extension
method a call does not see leaves it a member call, which the receiver's
type then refuses as before (`int has no method 'M'`). In a class, the
class's own extension methods are its methods (a closure over `Self`), so
a call `X.M(…)` in the class's methods is `$ext:M(X, …)` of `Self`.

**The receiver's members.** At the function call the elaborator types the
receiver once. If its type has no member `M`, the call is the function's.
If it has one (a field, a method, an inherited one, a built-in method of an
array, a char, a number or a task), the call is the one of the two it fits,
each tried as overload resolution tries an overload; fitting both is
ambiguous (3518). An extension method on a class or interface that has a
method `M` a call could not tell apart from it is refused where it is
defined (3532).

**A bare call in a method**, `M(…)` with an extension method `M` in scope,
is the extension method's call with `Self` or the call as written,
whichever it fits, and ambiguous when it fits both (`SOL-3515`).

**Refused.** `X.M` not called, when `M` is an extension method's (ch. 6
"must be called"); a receiver that is not one parameter, a named one or one
with a default; `(R:t).M:t` (no extension fields); a reserved name; a
`<constructor>`.

**Where the proposed reading does not hold.** "An ordinary function whose
first parameter is the receiver, found by method-call syntax when the
receiver's type has no member of that name" holds for overloading,
generics, effects, parameters and bodies. It needs three corrections:

1. *Not callable as a function, and no value.* `M(X)` does not reach it, and
   `M` names no value (ch. 6:653-671): its name is one no program writes.
   This also keeps it out of the overloads of an ordinary function `M`,
   which Verse keeps apart (Verse's own function takes the receiver and an
   argument tuple, two parameters, so `(X:int).M()` and `M(X:int)` never
   overlap).
2. *Members and extension methods are candidates of one call.* "When the
   receiver's type has no member" is right when only one fits; when the
   extension method fits as well, the call is ambiguous
   (`ExtensionFields.versetest:106-124`), when only it fits it is called
   (a method `Put(I:int)` and an extension `(B:box).Put(S:string)`), and a
   class's own method may not be repeated (3532).
3. *A bare call in a method.* The tests call an extension method of `Self`'s
   class without a receiver (`SOL-3515`), as a method is.

**Built-in methods under the same rule.** The char conversions are
extension methods in the API reference, and the array methods are "the
array extension `Last`" (ch. 16:578). In openverse they are compiled where
they are called (`scalarMethod?`, `elabMethod`), with Verse Core's
operations inline. Under this design they are members of their receiver
types for the one lookup a call makes (`Ctx.hasOwnMember`): a program's
extension method of the same name on another type is called, and one that
takes the same receiver makes the call ambiguous, as two extension methods
would. Making them declarations of a prelude, `(Byte:char).ToCodeUnit()<computes>:int =
…`, would make each call a call of a function, so every program that uses
one would change its bytecode, and the inline array methods would need
generic functions with `<decides>` bodies of their own: a follow-up.

## Readings openverse takes

- **Innermost first.** As for a function's name, the first scope outward
  that has `$ext:M` (its own definitions, then the modules it opens) gives
  the call's overloads; two modules opened at one scope that both give it
  make the call ambiguous. Verse may gather overloads from several scopes;
  the Book says nothing of it.
- **`tuple()` is `void`**, which overlaps every type in an overload, so
  `(X:tuple()).Extension()` beside `(A:int).Extension()`
  (`ExtensionFields.versetest:45-47`, valid there) is refused as two
  overloads a call cannot tell apart, as `F(X:tuple())` beside `F(A:int)`
  is ([Overloading](../LANGUAGE.md#overloading)).
- **"The same signature"** (3532) is read as openverse's overload rule: a
  call could fit both.
- **A field counts as a member**: `X.F(…)` with a field `F` is the field's
  call or index, unless only an extension method `F` fits.
- **An extension method in a class** is a method of the class: it is called
  in the class's methods, with `Self`, and is not visible outside.
- **`<override>`**, on an extension method in a class, overrides as a
  method's would; the Book does not describe it, and nothing tests it.

## The Book's tests

With the survey's harness ([After extension
methods](book-test-conformance.md#after-extension-methods)): 37 cases more
agree (33 the survey counted under extension methods, 4 under unnamed
parameters), none fewer, and none became an accepted refusal or a
different result; 11 expected errors that agreed by a parse error of the
form now agree by the rule they test. The test runner's own extension
methods (`TakeExtension`, `PlusTwo`, `TestParametricExtensionMethod`) are
not translatable.

## What is left

- **Qualified extension methods**, `X.(Utils:)Shout()` and the path
  qualifiers of `Bugs/SOL-8768-QualificationOfExtensionFields.versetest`
  (`(InPlayer:player).(/Verse.org/VerseTests/MyModule:)DoSomething`): the
  qualified names' work, which would let `(M:)` select `M::$ext:F`.
- **`tuple()` as a type of its own**, apart from `void`: an owner decision
  (3 cases).
- **A receiver typed by its context**: `map{}.RemoveKey[0]` with
  `(Input:[int]u where u:type)`, where Verse's empty map has a type of its
  own (1 case; empty containers).
- **Several values and a member of one name.** The choice inliner takes a
  call `$ext:M(X, …)` of an extension method with several values before
  the elaborator sees `X`'s type, so `X`'s own member `M` is not considered
  there: `c{}.Vals()` is refused ("expected int, found c") when `c` has a
  method `Vals()` and an extension method `(I:int).Vals()` has several
  values, and taken by a generic one, `(X:t where t:type).Vals()`, where
  Verse would call it ambiguous. A method with several values, `Vals()`,
  is not inlined either when an extension method `Vals` is in scope (the
  call is refused). Each needs the elaboration's answer before the
  inliner, a request of a round of its own; no test has either.
- **Messages** do not say that an extension method exists but is not
  visible (`int has no method 'Ext'`), nor name the receiver when its type
  is the one an extension method's overloads do not take.
