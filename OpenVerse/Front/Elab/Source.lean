/- Elaboration of a program's source, before its classes and types (phases 1–3 of
   `elabProgramCore`); public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Lowering
import OpenVerse.Front.InitializerConvergence

namespace OpenVerse.Front
open OpenVerse

/-- A program's source admitted (`admitSource`): checked against the effect
    policy and the source profile, modules resolved, and the compiler's own
    definitions it needs. -/
structure Admitted where
  /-- The program's definitions, modules resolved (#112), then the entry
      expression's function `$Do`, if any. -/
  resolved : List STop
  /-- The entry expression's function, or nothing: the end of `resolved`. -/
  rawEntry : List STop
  /-- The compiler's definitions the program needs: the rationals' (#116),
      `ReplaceAll`'s, the concurrency prelude's (#156) and subscribable
      events' (#210, #220). -/
  helpers : List STop
  /-- The functions of `helpers` that implement finite intrinsic operations
      (`InitializerConvergence`). -/
  intrinsicCalls : List String
  /-- The prelude's names the program defines itself, each with the name the
      prelude's own definition takes. -/
  concurrencyNames : List (String × String)
  /-- Whether the program uses concurrency (#156), so is lowered for it. -/
  usesConc : Bool
  /-- The construction effects each class and struct of the source declares
      (`EffectPolicy.constructionFx`), by its name. -/
  constructionFx : Std.HashMap String (List String)

/-- Source admission and the prelude, the first phase of `elabProgramCore`:
    the source and the entry expression are admitted by the effect policy and
    the source profile; the program's own types do not take built-in names;
    modules are resolved (#112); and the helpers the program needs are added,
    those the source names alike kept apart from them (#210). -/
def admitSource (allTops0r : List STop) (opts : Options) : Except String Admitted := do
  EffectPolicy.check allTops0r opts.entry
  SourceProfile.check opts.profile allTops0r opts.entry
  -- rationals (#116): the helpers, for a program that may use them
  let isRatMarker : STop → Bool := fun
    | .const _ n _ _ => n == ratMarker || n == replaceAllMarker
    | _ => false
  let usesReplaceAll := allTops0r.any (fun | .const _ n _ _ => n == replaceAllMarker | _ => false) || opts.entry.isSome
  let usesRat := allTops0r.any isRatMarker || opts.entry.isSome
  -- (a type of the program's own cannot take a built-in type's name)
  for t in allTops0r do
    match t with
    | .const p n _ (.structDef ..) | .const p n _ (.enumDef ..) | .classDef p n .. =>
      if ("char32" :: typeNames).contains n then throw s!"{p.show}: {n} is a built-in type"
    | _ => pure ()
  let helpers ← if usesRat then ratTops else pure []
  let helpers := helpers ++ (← if usesReplaceAll then replaceAllTops else pure [])
  -- These compiler-owned implementations expand finite intrinsic operations:
  -- Euclid/continued fractions decrease absolute remainders; ReplaceAll
  -- advances through a finite input. Ordinary source names cannot supply them.
  let intrinsicCalls := helpers.filterMap fun | .fn _ n .. => some n | _ => none
  let allTops000 := allTops0r.filter (!isRatMarker ·)
  -- modules (#112): every reference to a member, qualified (the entry
  -- expression's too)
  let rawEntry : List STop := match opts.entry with
    | some e => [.fn e.pos "$Do" [] [] ["decides"] (.name "void") (.app e.pos (.ident e.pos "$Show") [e] false)]
    | none => []
  let resolved ← resolveModules (allTops000 ++ rawEntry)
  let resolved := if opts.extendedDefaults then resolved
    else resolved.map InitializerConvergence.markSource
  -- Resolve source names before deciding which soft-library definitions are
  -- needed. A module's own event and a type parameter named task are distinct
  -- from the global helper types. Include public API/generated entry paths.
  let defines0 (n : String) : Option Pos := resolved.findSome? fun
    | .classDef p m .. | .fn p m .. | .const p m .. => if m == n then some p else none
  let owned := PreludeNeeds.names.filter (defines0 · |>.isSome)
  let requestTops := opts.requests.subtypes ++ Refine.functions opts.requests.casts resolved ++
    opts.requests.loops.flatMap (fun l =>
      STop.fn l.pos l.name l.params l.tparams l.specs l.ret l.body :: l.extraFns) ++
    opts.requests.methods.map (fun r => STop.fn r.pos "$methodRequest"
      ((r.receiver :: r.params).map fun t => { name := "$arg", ty := t }) r.tparams r.effs r.ret (.block r.pos r.args))
  let uses := PreludeNeeds.uses (resolved ++ requestTops) ++
    opts.requests.fns.flatMap (fun (_, t) => t.helperUses)
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
  -- Keep source overrides, but isolate helper dependencies from them: builtin
  -- sticky_event still extends the builtin event when source owns event.
  let helpers := helpers ++ (← if usesConc then concTops privateNames opts.eventFifo else pure []) ++
    (← if usesSub then subTops privateNames else pure []) ++ (← if usesSubVoid then subVoidTops privateNames else pure [])
  -- Collect source contracts while every declaration still has its source
  -- identity. Function-value classes, continuation frames and constructor
  -- field packets implement source expressions; they acquire no extra source
  -- contract merely because their implementation uses a data type.
  let constructionFx := resolved.foldl (fun budgets top => match top with
    | .classDef _ n _ specs .. | .const _ n _ (.structDef _ _ specs _) =>
      budgets.insert n (EffectPolicy.constructionFx specs)
    | _ => budgets) ({} : Std.HashMap String (List String))
  return { resolved, rawEntry, helpers, intrinsicCalls, concurrencyNames, usesConc, constructionFx }

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
def inlineSource (allTops0r : List STop) (requests : Requests) (admitted : Admitted) :
    Except String Source := do
  -- functions with several values (#235): inlined at their calls
  -- (#283) the members of built-in types and of the prelude: a method with
  -- several values may not be named like one, as `R.M` could be it
  let reserved : List String := ["Length", "Slice", "Find", "Insert", "Remove", "RemoveElement",
    "RemoveFirstElement", "RemoveAllElements", "ReplaceElement", "ReplaceAllElements", "ReplaceAll", "Last",
    "Signal", "Await", "Cancel"] ++ admitted.helpers.flatMap fun
      | .classDef _ _ _ _ _ _ fs _ ms => fs.map (·.1) ++ ms.filterMap fun | .fn _ m .. => some m | _ => none
      | _ => []
  -- (#283) and the uses of methods whose family the receiver's class picks,
  -- and the calls whose overload the arguments' types pick
  -- (#283) and the consumers in recursive groups' code whose names' types
  -- an elaboration is to note
  let ⟨resolved, lazy, familySites, overloadSites, nestedSites, fieldSites⟩ ← Choice.inlineMulti admitted.resolved reserved
    requests.eager requests.families requests.lazy requests.overloads requests.nested
    requests.fieldOrders
  -- (#246) the class of the stack cells of lazily taken ones
  let helpers := admitted.helpers ++ (← if lazy then lazyTops else pure [])
  -- (#283) and of the cells of the vars their frames set
  let cells (e : SExpr) : Bool := Choice.anyE (fun | .construct _ "$varcell" .. => true | _ => false) e
  let cellsIn (ps : List SParam) (b : SExpr) : Bool := cells b || ps.any (·.default.any cells)
  let usesCells := lazy && resolved.any fun
    | .fn _ _ ps _ _ _ b => cellsIn ps b
    | .const _ _ _ e => cells e
    | .classDef _ _ _ _ _ _ fs _ ms => fs.any (·.2.2.1.any cells) ||
        ms.any fun | .fn _ _ ps _ _ _ b => cellsIn ps b | _ => false
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
          !name.startsWith "$subtypeRefinement" then
        throw s!"{p.show}: internal: invalid subtype dictionary request"
    | _ => throw "internal: a subtype dictionary request must be a class"
  let resolved := requests.subtypes ++ loopTops ++ resolved
  let needsSubtype := allTops0r.any UpperBounds.hasBounds || !requests.subtypes.isEmpty ||
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
      | .classDef _ n _ specs .. | .const _ n _ (.structDef _ _ specs _) => some (n, specs)
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
  let allTops00 := copyIfaceDefaults (SubtypeEvidence.addFields
    (FnValues.desugar (resolved.take (resolved.length - admitted.rawEntry.length) ++ helpers)
      (resolved.drop (resolved.length - admitted.rawEntry.length)) (requests.fns.map fun (n, t) => (n, t.toSTy)) requests.methods))
  let entryTop := resolved.drop (resolved.length - admitted.rawEntry.length)
  return { tops := allTops00, entry := entryTop, constructionFx, familySites, overloadSites, nestedSites,
           fieldSites }

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
  let argsTop : List STop :=
    match args with
    | some as =>
      if defines "Args" then []
      else [.const { line := 0, col := 0 } "Args" (some (.arr (.name "string")))
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
