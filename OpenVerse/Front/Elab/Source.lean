/- Elaboration of a program's source, before its classes and types (phases 1–3 of
   `elabProgramCore`); public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Lowering
import OpenVerse.Front.InitializerConvergence
import OpenVerse.Front.Aliases
import OpenVerse.Front.BuiltinValues
import OpenVerse.Front.FinalSuper
import OpenVerse.Front.Bitwise
import OpenVerse.Front.Localization
import OpenVerse.Front.TypeValues
import OpenVerse.Front.TypeArguments
import OpenVerse.Front.SourceRules

namespace OpenVerse.Front
open OpenVerse

/-- A program's source admitted (`admitSource`): checked, its names resolved
    and its desugarings done, with the compiler's own definitions it needs. -/
structure Admitted where
  /-- The program's definitions, modules resolved (#112), then the entry
      expression's function `$Do`, if any. -/
  resolved : List STop
  /-- The entry expression's function, or nothing: the end of `resolved`. -/
  rawEntry : List STop
  /-- The defaults function types write (#503, `STop.isTypeDefault`), set apart
      from the definitions: `inferSignatures` checks them. -/
  typeDefaults : List STop
  /-- The compiler's definitions the program needs: the rationals' (#116),
      `ReplaceAll`'s, the bitwise functions', the concurrency prelude's
      (#156) and subscribable events' (#210, #220). -/
  helpers : List STop
  /-- The functions of `helpers` that implement finite intrinsic operations
      (`InitializerConvergence`). -/
  intrinsicCalls : List String
  /-- The prelude's names the program defines itself, each with the name the
      prelude's own definition takes. -/
  concurrencyNames : List (String × String)
  /-- Whether the program uses concurrency (#156), so is lowered for it. -/
  usesConc : Bool
  /-- Whether it uses an event type, so is lowered in event mode: a
      `Signal` resumes its awaiters inside it (the Book's API, `event`'s
      `Signal`; `concPreludeEvents`). -/
  usesEvents : Bool := false
  /-- The functions defined in a module or a class with the name of a
      function around them, which no call may fit both of
      (`checkNoShadowing`, `checkSignatures`). -/
  scopePairs : List ScopePair := []
  /-- The construction effects each class and struct of the source declares
      (`EffectPolicy.constructionFx`), by its name. -/
  constructionFx : Std.HashMap String (List String)
  /-- What the elaboration needs to judge a use of a class's member (`Access.Env`). -/
  access : Access.Env := {}
  /-- The `case` arms marked `@ignore_unreachable` (`ignoredArmsMarker`). -/
  ignoredArms : List Pos := []
  /-- The places of the filters of every `for` and `first` with a generator
      as written, with their kinds (`forFilterPositions`). -/
  forFilters : List (Pos × String) := []
  /-- The type aliases, each by its name, written out (`Aliases.expand`). -/
  aliases : List (String × Aliases.Alias) := []

/-- The concurrency prelude a program needs (#156), with subscribable
    events' (#210, #220): the prelude's names the program defines itself,
    each with the name the prelude's own definition takes, whether the
    program uses concurrency, and the prelude's definitions. It reads the
    program's names resolved (a module's own `event`, a type parameter named
    `task`, are not the prelude's), and the functions the requests add. -/
def concurrencyHelpers (resolved : List STop) (requests : Requests) :
    Except String (List (String × String) × Bool × Bool × List STop) := do
  let defines0 (n : String) : Option Pos := resolved.findSome? fun
    | .classDef p m .. | .fn p m .. | .const p m .. => if m == n then some p else none
  let owned := PreludeNeeds.names.filter (defines0 · |>.isSome)
  let requestTops := requests.subtypes ++ Refine.functions requests.casts resolved ++
    requests.loops.flatMap (fun l =>
      STop.fn l.pos l.name l.params l.tparams l.specs l.ret l.body :: l.extraFns) ++
    requests.methods.map (fun r => STop.fn r.pos "$methodRequest"
      ((r.receiver :: r.params).map fun t => { name := "$arg", ty := t }) r.tparams r.effs r.ret (.block r.pos r.args))
  let uses := PreludeNeeds.uses (resolved ++ requestTops) ++
    requests.fns.flatMap (fun (_, t) => t.helperUses)
  let privateNames := PreludeNeeds.privateNames owned uses
  let concurrencyNames := privateNames.map fun n => (n, "$" ++ n)
  let needs (n : String) := uses.contains ((concurrencyNames.lookup n).getD n)
  let usesSubVoid := uses.contains "$subev0"
  if usesSubVoid && owned.contains "subscribable_event" then
    throw "subscribable_event() is the built-in no-payload shorthand; apply a program's own subscribable_event with explicit type arguments"
  let usesSub := usesSubVoid || needs "subscribable_event" || needs "cancelable"
  if usesSub then
    if let some p := defines0 "cancelable" then
      throw s!"{p.show}: cancelable is the type subscribable_event's Subscribe gives: a program that uses subscribable_event cannot define its own (#210)"
  let usesConc := usesSub || uses.contains "$suspends" || PreludeNeeds.names.any needs
  -- (the program's own definitions of the prelude's names kept apart from
  -- the prelude's: its sticky_event extends its own event when the program
  -- defines one)
  -- (event mode: a program that uses an event type, whose `Signal` resumes
  -- the awaiters inside it, `concPreludeEvents`)
  let usesEvents := usesConc && (usesSub || needs "event" || needs "sticky_event")
  let helpers := (← if usesConc then concTops privateNames usesEvents else pure []) ++
    (← if usesSub then subTops privateNames else pure []) ++ (← if usesSubVoid then subVoidTops privateNames else pure [])
  return (concurrencyNames, usesConc, usesEvents, helpers)

/-- Source admission, the first phase of `elabProgramCore`: the program as
    parsed (its attributes taken out, `Attributes.apply`), checked, resolved
    and desugared by these passes, in this order, which is the order of their
    refusals:
    0. localized messages written out (`Localization.desugar`), their
       helpers added at 3;
    1. the effect policy, with where each specifier may go, and the source
       profile (`EffectPolicy`, `SourceProfile`);
    2. the rules of the source as written (`SourceRules.lean`, in this
       order): no built-in type's name taken by a type
       (`checkTypeNames`), no reserved name (`checkReservedNames`), no
       built-in type's name by any other definition
       (`checkBuiltinTypeNames`), each name defined once in its
       scope (`checkDefinedOnce`) and none of a scope around it
       (`checkNoShadowing`), `return` only in a function
       (`checkReturns`), no `return` or `break` that leaves a failure
       context (`checkJumps`), none inside a value returned
       (`checkNestedReturns`) or leaving a `spawn` (`checkSpawnExits`), a
       way out of each loop of code that cannot suspend (`checkLoopExits`),
       `(super:)M` only in an override of `M` (`checkSuperCalls`),
       the five forms the Book's tests refuse (`checkBookForms`: a default
       on a positional parameter, a named argument before a positional one,
       a struct's `var` field, a jump out of a construction's field value,
       an empty `option{}`), `profile` only in a function's code
       (`checkProfiles`), `defer:` only as a statement (`checkDefers`), no
       `for` of literal clauses only, nor a literal filter
       (`checkForClauses`), and the places of the filters of every `for`
       and every `first` with a generator (`forFilterPositions`), whose code
       the elaboration checks can fail;
    3. the helpers the parser's `$uses:` markers and the entry expression ask
       for, and the markers taken out;
    4. the access levels written out (`resolveSpecifiers`), then the modules
       and qualifiers resolved, the entry expression's too (`resolveModules`);
    5. type aliases no more visible than what they name
       (`Access.checkAliases`), then written out where they are used
       (`Aliases.expand`);
    6. no definition exposing a less visible one (`Access.checkConsistency`),
       and constructions, parents and overrides used where they may be
       (`Access.checkUses`, with `Access.Env`, which the elaboration reads);
    7. the desugarings: module-scoped `var`s, checked and made the `var`
       fields of the module state's object (`ModuleVars`), types given as
       arguments (`TypeArguments`), the calls of the final super class
       queries (`FinalSuper`), types as values (`TypeValues`), fields
       with accessors (`Accessors`), castable bounds
       (`UpperBounds.markCastable`), built-ins named as values
       (`BuiltinValues`);
    8. the defaults function types write set apart, no constant that depends
       on itself (`checkConstantCycles`) or names one after it in its scope
       (`checkConstantOrder`; both in `SourceRules.lean`), and the calls of initializers marked
       (`InitializerConvergence.markSource`);
    9. the concurrency prelude the program needs (`concurrencyHelpers`), and
       the construction effects the source declares. -/
def admitSource (written : List STop) (opts : Options) : Except String Admitted := do
  -- 0. localized messages written out (`Localization`): `<localizes>`
  --    definitions as the strings of their default text, `Localize` and
  --    `Join` as calls of their helpers
  let (allTops0r, usesLocalization) ← Localization.desugar written
  -- 1. effects and specifiers, and the source profile
  EffectPolicy.check allTops0r opts.entry
  EffectPolicy.checkPlaces allTops0r
  SourceProfile.check opts.profile allTops0r opts.entry
  -- 2. the rules of the source as written, on the definitions as parsed
  --    (`SourceRules`)
  checkTypeNames allTops0r
  checkReservedNames allTops0r
  checkBuiltinTypeNames allTops0r
  checkDefinedOnce allTops0r
  let scopePairs ← checkNoShadowing allTops0r
  checkReturns allTops0r
  checkJumps allTops0r
  checkNestedReturns allTops0r
  checkSpawnExits allTops0r
  checkLoopExits allTops0r
  checkSuperCalls allTops0r
  checkBookForms allTops0r
  checkProfiles allTops0r
  checkDefers allTops0r
  checkForClauses allTops0r
  -- 3. the helpers the markers and the entry expression ask for: the
  --    rationals' (#116), ReplaceAll's, the bitwise
  --    functions'. They expand finite intrinsic operations
  --    (`intrinsicCalls`): Euclid/continued fractions decrease absolute
  --    remainders; ReplaceAll advances through a finite input; the bitwise
  --    helpers halve or double an int64 at most 64 times (a left shift ends
  --    at the overflow error by then). Ordinary source names cannot supply
  --    them.
  let marked (m : String) : Bool := allTops0r.any fun | .const _ n _ _ _ => n == m | _ => false
  let usesRat := marked ratMarker || opts.entry.isSome
  let usesReplaceAll := marked replaceAllMarker || opts.entry.isSome
  let usesBitwise := marked bitwiseMarker || (opts.entry.map mentionsBitwise).getD false
  -- (`ToDiagnostic`'s, unless the program defines one of the Book's names
  -- they give itself: then its own are the ones it calls)
  let definesDiagnostic := allTops0r.any fun
    | .fn _ n .. | .const _ n .. | .classDef _ n .. => Diagnostic.bookNames.contains n
  let usesDiagnostic := (marked diagnosticMarker ||
    (opts.entry.map (Choice.anyE fun | .ident _ n => n == "ToDiagnostic" | _ => false)).getD false) &&
    !definesDiagnostic
  let helpers := (← if usesRat then ratTops else pure []) ++ (← if usesReplaceAll then replaceAllTops else pure []) ++
    (← if usesBitwise then bitwiseTops else pure []) ++
    (← if usesLocalization then Localization.tops else pure [])
  let intrinsicCalls := helpers.filterMap fun | .fn _ n .. => some n | _ => none
  -- (not `ToDiagnostic`'s: it calls a `diagnosable` object's own method,
  -- which may not converge)
  let helpers := helpers ++ (← if usesDiagnostic then Diagnostic.tops else pure [])
  let ignoredArms := ignoredArmsOf allTops0r
  let unmarked := allTops0r.filter fun
    | .const _ n _ _ _ => ![ratMarker, replaceAllMarker, ignoredArmsMarker, bitwiseMarker, diagnosticMarker].contains n
    | _ => true
  -- 4. access levels written out (Book of Verse ch. 12), and the levels of
  --    the definitions and modules; modules (#112): every reference to a
  --    member qualified, the entry expression's function `$Do`'s too
  let rawEntry : List STop := match opts.entry with
    | some e => [.fn e.pos "$Do" [] [] ["decides"] (.name "void") (.app e.pos (.ident e.pos "$Show") [e] false)]
    | none => []
  let specified ← resolveSpecifiers (unmarked ++ rawEntry)
  let levels := Access.Levels.of specified
  let resolved ← resolveModules specified
  -- 5. type aliases: no more visible than what they name; each written out
  --    where it is used, so that nothing after this knows aliases exist
  Access.checkAliases levels resolved
  let (resolved, aliases) ← Aliases.expand resolved
  -- 6. access: each definition exposes nothing less visible than itself;
  --    the constructions, parents and overrides of the program as written;
  --    and what the elaboration needs to judge the members it reaches
  --    through values
  Access.checkConsistency levels resolved
  let access := Access.Env.of levels (Access.Sites.of resolved) resolved
  Access.checkUses access resolved
  -- 7. module-scoped `var`s: checked, and held as the `var` fields of the
  --    module state's object, each use one through it
  --    (docs/research/weak-map.md); types given as arguments and used as
  --    types: type parameters; types
  --    as values, `subtype(t)` and its kin: classes and interfaces; fields
  --    with accessors: checked, and their accessors' type written; a
  --    castable_subtype(c) bound's castability: a subtype relation; the
  --    built-ins the program names as values: definitions of their own
  --    (after the aliases, whose names are no values' and bind nothing)
  let resolved ← ModuleVars.desugar resolved
  let resolved ← TypeArguments.desugar resolved
  let resolved ← FinalSuper.desugar resolved
  let resolved ← TypeValues.desugar resolved
  let resolved ← Accessors.desugar resolved
  let resolved := UpperBounds.markCastable resolved
  let resolved := BuiltinValues.wrappers resolved ++ resolved
  -- 8. the defaults function types write, for `inferSignatures`; the
  --    constants' dependencies; initializers' calls marked
  let (typeDefaults, resolved) := resolved.partition (·.isTypeDefault)
  checkConstantCycles resolved
  checkConstantOrder resolved
  let resolved := if opts.extendedDefaults then resolved
    else resolved.map InitializerConvergence.markSource
  -- 9. the concurrency prelude; and the source's construction effects,
  --    collected while every definition still has its source identity:
  --    function-value classes, continuation frames and constructor field
  --    packets implement source expressions, and acquire no contract
  --    merely because their implementation uses a data type
  let (concurrencyNames, usesConc, usesEvents, prelude) ← concurrencyHelpers resolved opts.requests
  let constructionFx := resolved.foldl (fun budgets top => match top with
    | .classDef _ n _ _ specs .. | .const _ n _ _ (.structDef _ _ specs _) =>
      budgets.insert n (EffectPolicy.constructionFx specs)
    | _ => budgets) ({} : Std.HashMap String (List String))
  return { resolved, rawEntry, typeDefaults, helpers := helpers ++ prelude, intrinsicCalls, concurrencyNames, usesConc, usesEvents,
           constructionFx, access, scopePairs, ignoredArms, aliases, forFilters := forFilterPositions allTops0r }

/-- A program's source as elaborated (`inlineSource`). -/
structure Source where
  /-- The definitions: the source's, choices inlined (#283), with the functions
      requested (the branches of refining casts, #243, the functions of lazily
      taken calls, #246, subtype dictionaries, #520), function values'
      interfaces and classes (#210), and the helpers; not the entry expression. -/
  tops : List STop
  /-- The entry expression's function, or nothing. -/
  entry : List STop
  /-- `Admitted.constructionFx`, and those that materialized requests declare. -/
  constructionFx : Std.HashMap String (List String)
  /-- `Admitted.access`. -/
  access : Access.Env := {}
  /-- `Admitted.ignoredArms`. -/
  ignoredArms : List Pos := []
  /-- `Admitted.forFilters`. -/
  forFilters : List (Pos × String) := []

  /-- The uses of methods whose family the receiver's class picks (#283). -/
  familySites : List (Pos × String)
  /-- The calls whose overload the arguments' types pick (#283). -/
  overloadSites : List (Pos × String)
  /-- The consumers in recursive groups' code whose names' types an
      elaboration is to note (#283). -/
  nestedSites : List String
  /-- The structs and classes that code constructs with a choice point in a
      field, whose field orders an elaboration is to note (#283). -/
  fieldSites : List String

/-- Choice inlining and materialized requests, a phase of `elabProgramCore`:
    functions with several values are inlined at their calls (#235, #283), as
    `requests` says which are eager, lazy, of which family or overload; the
    functions requested are added and admitted by the effect policy; and
    function values become interfaces and classes (#210). -/
def inlineSource (requests : Requests) (admitted : Admitted) :
    Except String Source := do
  -- functions with several values (#235, #283), inlined at their calls; a
  -- method with several values may not take the name of a member of a
  -- built-in type or of the prelude, as `R.M` could be it
  let reserved : List String := ["Length", "Slice", "Find", "Insert", "Remove", "RemoveElement",
    "RemoveFirstElement", "RemoveAllElements", "ReplaceElement", "ReplaceAllElements", "ReplaceAll", "Last",
    "Signal", "Await", "Cancel"] ++ admitted.helpers.flatMap fun
      | .classDef _ _ _ _ _ _ _ fs ms => fs.map (·.1) ++ ms.filterMap fun | .fn _ m .. => some m | _ => none
      | _ => []
  -- (with the sites an elaboration is to note, #283: the uses of methods
  -- whose family the receiver's class picks, the calls whose overload the
  -- arguments' types pick, the consumers in recursive groups' code whose
  -- names' types it notes, the types whose field orders it notes)
  let written := admitted.resolved
  let ⟨resolved, lazy, familySites, overloadSites, nestedSites, fieldSites⟩ ← Choice.inlineMulti written reserved
    requests.eager requests.families requests.lazy requests.overloads requests.nested
    requests.fieldOrders requests.instanceCalls
  -- (#246) the class of the stack cells of lazily taken ones
  let helpers := admitted.helpers ++ (← if lazy then lazyTops else pure [])
  -- (#283) and of the cells of the vars their frames set
  let cells (e : SExpr) : Bool := Choice.anyE (fun | .construct _ "$varcell" .. => true | _ => false) e
  let usesCells := lazy && resolved.any (·.code.any cells)
  let helpers := helpers ++ (← if usesCells then varcellTops else pure [])
  -- the branches of casts that refine type arguments, as functions (#243)
  -- (in front, as the entry expression is the end)
  let resolved := Refine.functions requests.casts resolved ++ resolved
  -- (#246) the functions of their own of lazily taken calls
  let mut generated : List String := []
  let mut loopTops : List STop := []
  for top in requests.loops.flatMap (fun l =>
      (if l.stageOnly then [] else [STop.fn l.pos l.name l.params l.tparams l.specs l.ret l.body]) ++ l.extraFns) do
    let name := match top with
      | .fn _ n .. | .classDef _ n .. => n
      | _ => ""
    if name.startsWith "$choiceOperationDictionary" then
      if generated.contains name then continue
      generated := name :: generated
    loopTops := loopTops ++ [top]
  for request in requests.subtypes do
    match request with
    | .classDef p name .. =>
      if !name.startsWith "$subtypeNominal" && !name.startsWith "$subtypeTuple" &&
          !name.startsWith "$subtypeRefinement" && !name.startsWith "$subtypeBox" then
        throw s!"{p.show}: internal: invalid subtype dictionary request"
    | _ => throw "internal: a subtype dictionary request must be a class"
  -- (in a program that calls `ToDiagnostic`, the classes of the values
  -- converted to `any` and their printers)
  let resolved := requests.subtypes ++ requests.anys ++ loopTops ++ resolved
  -- (bounds as written, or a bounded type given as an argument's,
  -- `TypeArguments`: the source's before its choices are inlined, and after)
  let needsSubtype := written.any UpperBounds.hasBounds || resolved.any UpperBounds.hasBounds ||
    !requests.subtypes.isEmpty ||
    -- (the box of a type parameter's value is its comparable bound's evidence)
    !requests.boxes.isEmpty ||
    resolved.any (·.usesType SubtypeEvidence.family)
  let definesSubtype := (resolved ++ helpers).any fun
    | .classDef _ name .. => name == SubtypeEvidence.family
    | _ => false
  let helpers := helpers ++ (if needsSubtype && !definesSubtype then
    SubtypeEvidence.protocol { line := 0, col := 0 } else [])
  -- Public compiler requests must not launder annotations through generated
  -- source or through function shapes that normalize their effect lists.
  EffectPolicy.check (resolved ++ helpers)
  -- A materialized request can itself carry an explicit data contract.
  -- Enforce it too; unannotated implementation types retain inferred effects.
  let constructionFx := (resolved ++ helpers).foldl (fun budgets top =>
    let data := match top with
      | .classDef _ n _ _ specs .. | .const _ n _ _ (.structDef _ _ specs _) => some (n, specs)
      | _ => none
    match data with
    | some (n, specs) =>
      if budgets.contains n || !specs.any EffectPolicy.effectNames.contains then budgets
      else budgets.insert n (EffectPolicy.constructionFx specs)
    | none => budgets) admitted.constructionFx
  for (_, ty) in requests.fns do
    EffectPolicy.checkTy { line := 0, col := 0 } ty.toSTy
  for request in requests.methods do
    EffectPolicy.checkSpecs request.pos request.key request.effs
    EffectPolicy.checkTParams request.tparams
    EffectPolicy.checkTy request.pos request.receiver
    request.params.forM (EffectPolicy.checkTy request.pos)
    EffectPolicy.checkTy request.pos request.ret
    request.args.forM (EffectPolicy.checkExpr · request.pos.file)
  -- (the helpers after: they name nothing of the program's)
  -- function values (#210): the function types' interfaces, and a class
  -- for each function used as a value
  -- (the entry expression is scanned too)
  let allTops00 := (SubtypeEvidence.addFields
    (FnValues.desugar (resolved.take (resolved.length - admitted.rawEntry.length) ++ helpers)
      (resolved.drop (resolved.length - admitted.rawEntry.length)) (requests.fns.map fun (n, t) => (n, t.toSTy))
      requests.methods written))
  let entryTop := resolved.drop (resolved.length - admitted.rawEntry.length)
  return { tops := allTops00, entry := entryTop, constructionFx, access := admitted.access,
           ignoredArms := admitted.ignoredArms, forFilters := admitted.forFilters, familySites,
           overloadSites, nestedSites, fieldSites }


/-- A program's definitions complete (`argsAndMethodOverloads`), as the class
    phases start from them. -/
structure Definitions where
  /-- The definitions, `Args` and the entry expression's `$Do` included, each
      overloaded method renamed by its parameter list (`M$ovN`, #106). -/
  tops : List STop
  /-- The overloaded methods' parameter lists (`MethodOverloads`). -/
  methodOverloads : MethodOverloads

/-- `Args` and method overloads, a phase of `elabProgramCore`: the definitions
    `tops`, then `Args`, bound to the command line's arguments `args` (unless
    the program defines `Args`), then the entry expression's function `entry`;
    each method name declared with two or more parameter lists renamed by its
    list (#106). -/
def argsAndMethodOverloads (tops entry : List STop) (args : Option (List String)) :
    Except String Definitions := do
  -- the command line: `Args`, and an entry expression
  let defines (n : String) := tops.any fun
    | .fn _ m .. | .const _ m .. | .classDef _ m .. => m == n
  -- (`Args` is openverse's, the command line's, not the Book's: a program
  -- that binds the name itself, a local's or a parameter's too, has its
  -- own, `Args:tuple(int, int) = (1, 2)`, the Book's tests,
  -- `DefaultNamed.versetest:274`, `Math/Math.versetest:84`)
  let binds (n : String) := tops.any fun t =>
    (match t with
      | .fn _ _ ps .. => ps.any (·.name == n)
      | _ => false) ||
    t.code.any (Choice.anyE fun | .decl _ m _ _ _ => m == n | .gen _ m i _ => m == n || i == some n | _ => false)
  let argsTop : List STop :=
    match args with
    | some as =>
      if defines "Args" || binds "Args" then []
      else [.const { line := 0, col := 0 } "Args" [] (some (.arr (.name "string")))
              (.arrayLit { line := 0, col := 0 } (as.map fun a => .str { line := 0, col := 0 } [.text a]))]
    | none => []
  -- overloaded methods (#106): a method name declared with two or more
  -- parameter lists is renamed, in every class and interface, by its list
  -- (`M$ovN`, `MethodOverloads`): an override has its method's list, so its
  -- name too
  let mo := MethodOverloads.of (tops ++ argsTop ++ entry)
  let allTops0 ← mo.apply (tops ++ argsTop ++ entry)
  return { tops := allTops0, methodOverloads := mo }

end OpenVerse.Front
