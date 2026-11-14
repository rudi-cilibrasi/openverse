# `weak_map` and module-scoped `var`

What the Book of Verse says a `weak_map` is and where it may live, whether
its "weak key references" can be seen by any program, what a module-scoped
`var` is, and openverse's design (#491)
([LANGUAGE.md](../LANGUAGE.md#weak-maps),
[DESIGN.md](../DESIGN.md#weak-maps-and-module-scoped-vars)).

## Sources

- The [Book of Verse at `beaa719ba165cbf33eff462f2b0fe078a6dd9ab0`](https://github.com/verselang/book/tree/beaa719ba165cbf33eff462f2b0fe078a6dd9ab0/docs):
  chapter 3, "Weak Maps" (`docs/03_containers.md` lines 1090-1302, and
  line 3); chapter 16, "Module-Scoped Variables" (`docs/16_modules.md`
  lines 608-656); chapter 17 (`docs/17_persistable.md` lines 1-29, 170-280);
  chapter 18, "Persistent Variables" (`docs/18_evolution.md` lines 249-268);
  chapter 10, "Persistable" (`docs/10_classes_interfaces.md` lines
  2954-2998); chapter 9 (`docs/09_structs_enums.md` lines 95-108).
- The Book's API reference (`docs/api/verse_runtime_api.html`, and its
  notes `verse_api_overrides.md`): `weak_map`, the four `operator'()'`
  forms on maps and weak maps, `player`, `player.IsActive`, `session`,
  `FitsInPlayerMap`.
- The same snapshot's tests, by line: `Tests/weak_map.versetest` (96
  cases), `Tests/Map.versetest` 381-416 and 464-466,
  `Tests/GlobalVariables.versetest`, `Tests/persistable.versetest` 83,
  `Tests/Bugs/SOL-7231-NamedParameterMeet.versetest`,
  `Tests/WebDataSyncService.versetest`,
  `Tests/CompatibilityConstraints.versetest` 1510-1830.
- How the Book's own code blocks become tests: its `bin/extract` (Book
  tooling, CC0): a block's type definitions (`x := class|struct|module|…`)
  go to module scope and every other line into the body of an `assert:`.
  So a `var` written at the left margin of a chapter's example is a
  *local* of that test unless it is inside a hoisted `module`.
- Retrieved 2026-11-13. No Epic source was read and no Epic engine was run.

## Quotations

- Ch. 3, line 3: "A `weak_map` is a map that does not keep its keys alive,
  and is the basis for persistent storage."
- Lines 1092-1094: "The `weak_map` type is a specialized supertype of `map`
  designed for persistent data storage with weak key references. It
  behaves similarly to ordinary maps for individual entry access, but
  deliberately restricts bulk operations. You cannot ask for its length,
  you cannot iterate over its entries, and you cannot use
  `ConcatenateMaps`. … A `weak_map` is declared with `weak_map(k,v)` and
  can be initialized from an ordinary `map{}`. Updating and accessing
  individual entries works the same way as regular maps", with
  `set MyWeakMap[0] = 1`, `MyWeakMap[0] = 1` and
  `set MyWeakMap = map{0 => 2}   # reassignment still works (for local variables)`.
- Line 1108: "Because `weak_map` is a supertype of `map`, you can assign
  regular maps to weak_map variables when needed, but you lose the ability
  to count or iterate once you are working with a weak map."
- Line 1112: "Bulk operations are what a `weak_map` gives up. There is no
  `Length` property, no iteration, no coercion to `comparable`, and no way
  to join one with a regular map to produce a regular map. Looking up a
  single key still works", with four refusals proved by the block's
  prepend (3506 `W.Length`, 3524 `for (Entry : W) {}`, 3509
  `C:comparable = W`, 3509 `Joined:[int]int = if (true?) then W else map{3 => 4}`).
- Line 1146: "When using `weak_map` as a module-scoped variable (for
  persistent data), there are additional restrictions. The complete map can
  neither be read nor replaced, while reading and writing one entry at a
  time is allowed" (3502 for `GetAll()<transacts>:weak_map(k85, int) = Scores`
  and for `set Scores = map{}` in a module); line 1178: "These restrictions
  exist because module-scoped weak_maps integrate with the persistence
  system, which only tracks individual entry updates, not complete map
  replacements."
- Line 1180: "For module-scoped `var weak_map` variables, both key and
  value types have strict requirements. The key type must carry the
  `<module_scoped_var_weak_map_key>` specifier" (3502 for a plain
  `class<unique><allocates><computes>` key); line 1202: "The value type must
  be persistable" (3502 for a plain struct value, with a `<persistent>` key).
- Lines 1228-1232: "Common key types that satisfy the requirements:
  `player` - The standard key type for player-specific data;
  `persistent_key` - Custom persistent keys with validity tracking;
  `session_key` - Transient keys that do not persist across sessions."
- Line 1236: "The `weak_map` type is **covariant** in its key type, meaning
  you can use a weak_map with a subclass key type where a parent class key
  type is expected. The same covariance lets a regular map be assigned to a
  weak_map with a compatible key type" (3509 for the other direction).
- Line 1271: "A persistable value type cannot have `var` fields, so there
  is no way to update one field of a stored struct in place. What you can
  do is replace the whole value, or reach through it with an index when the
  value is itself a container": `set Items[Key] = array{1, 2, 3}`,
  `set Items[Key][0] = 99`.
- Lines 1285, 1302: "Like all mutable state in Verse, `weak_map` updates
  participate in transaction semantics. If a `<decides>` expression fails,
  all changes are rolled back … This applies to complete map replacements
  (for local variables), individual entries, and updates that reach inside
  a stored value."
- Ch. 16, lines 610-616: "Variables defined at module scope are global to
  any game instance where the variable is in scope. Restrictions on
  module-scoped definitions: Direct `var` declarations of simple types
  (like `var X:int = 0`) are not allowed at module scope; Instances of
  `<unique>` classes with `<allocates>` can be created at module scope, as
  long as their construction does not actually allocate mutable memory; For
  persistent mutable state, use `weak_map` with appropriate key types."
- Ch. 18, line 251: "a persistent variable is a module-scoped `var` whose
  type is a `weak_map` keyed by a session or a player. A module-scoped
  `var` of any other type is rejected outright — the compiler asks for a
  "`session` or `player` key type" — and even a `weak_map` may only be read
  or written one key at a time." Its prepend: 3502 for `var Score:int = 0`
  in a module.
- Ch. 17, line 8: "Persistable data is stored using module-scoped
  `weak_map(player, t)` variables, where `t` is any persistable type. When a
  player joins a game, their previously saved data is automatically loaded
  into all module-scoped variables of type `weak_map(player, t)`"; line
  185: "`weak_map` - Weak references are not persistable" (3662 for a
  `<persistable>` class's field `Cache:weak_map(int, int)`).
- Ch. 10, lines 2989-2997: a `<persistable>` class must be `<final>`
  (3663), not `<unique>` (3664), and "Every data member must itself be
  persistable, which rules out `var` fields" (3662).
- API reference, `weak_map`: "The type constructor behind
  `weak_map(key_type, value_type)`. It appears where a type is expected
  rather than where a value is … A `weak_map` does not keep its keys
  alive: an entry disappears once nothing else refers to its key."
  `operator'()'(Map:weak_map(t,u), Key:t where t:subtype(comparable), u:type)<converges><decides><predicts>:u`:
  "Reads the value stored against `Key` … Fails when the key is absent —
  and in a `weak_map`, a key can become absent on its own once nothing
  else holds it alive." `operator'()'(Map:ref(weak_map(t,u),weak_map(t,v)), Key:t …)<converges><reads><decides><predicts>:ref(u,v)`:
  "the declaration behind persistent player data: `set PlayerData[Player] =
  Stats`. Inserting on write, and failing when a missing key is read,
  behave as they do for ordinary maps."
- API reference, `player`: `class<unique><epic_internal><persistent><module_scoped_var_weak_map_key>(agent)`;
  `IsActive`: "using an inactive `player` as such a key is a runtime error
  rather than a failure you can recover from"; "Because `player` is also
  `<persistent>`, a module-scoped `var weak_map` keyed on it must have a
  `persistable` value type". `session`: `class<unique><epic_internal><module_scoped_var_weak_map_key>`,
  "a session-keyed map with a single entry is a global in all but name.
  Unlike `player` it is not `<persistent>`, so values stored against it
  need not be persistable and are not saved anywhere".

## The rules, pinned

**The type.** `weak_map(k, v)` is a type written as a parametric type; `k`
must be comparable (the lookup's `t:subtype(comparable)`). `[k]v` is a
subtype of `weak_map(k, v)`; `weak_map(k, v)` is a subtype of
`weak_map(k', v)` when `k` is a subtype of `k'` (covariant keys: ch. 3
line 1236; `weak_map.versetest` 41, 48, 73-95 accept, 55 refuses the other
way, 3509). A `weak_map` is no `[k]v` (62, 3509) and no `comparable`
(156, 3509; prose line 1112). The value type: covariant as a map's (no
test either way; a value is immutable, as in `[k]v`, so openverse takes
it, below). It may be a type argument (`Identity(X:t where t:type):t`,
138, 145) and a value of it an `any`. A join of a `weak_map` and a map is a
`weak_map` (98 succeeds; 104, 3510, and prose 1112 refuse it as a `[int]int`);
the meet of a `[int]int` and a `weak_map(int, int)` parameter is a
`[int]int` (113 succeeds, 117 refuses passing a `weak_map` to it, 3509).
It is not persistable (ch. 17 line 185; `persistable.versetest:83`, 3662).

**What it can do.** Entry lookup `W[k]` (fails when absent: 36, 38-39,
`Map.versetest:385`), entry update `set W[k] = v` (inserts or replaces),
paths through an entry (`set X[0].Data1 = 3`, 194-203; `set Items[Key][0]
= 99`, ch. 3 line 1280), whole reassignment of a *local* `var`
(`set X = map{3 => 4}`, 161-165; ch. 3 line 1104), and rollback of all of
these (206-227; ch. 3 lines 1285-1302). A key of a supertype of the map's
key reads (`Map.versetest:388`, `X[OtherKey]` with `OtherKey:class1` and
keys of `class2`); one of a sibling class does not write
(`Map.versetest:410`, 3509). `weak_map(comparable, int)` takes `set
ObjectMap[0] = 1` (`Map.versetest:464`).

**What it cannot do**, each a compile-time error: `.Length` (3506: there
is no such member, 125; prose 1112), iteration (3524, 130; prose 1112),
`ConcatenateMaps` (prose 1092; its parameters are maps), conversion to a
map or to `comparable` (3509, 62, 156), and equality (`=` needs
`comparable`). There is **no removal**: a map's entry is removed by
building a map without it, by iteration (ch. 3 lines 744-755), which a
`weak_map` has none of; a local is replaced whole.

**Where it may live.** A local (`var` or not), a parameter or result, a
field of a class (`SOL-7231`'s `var Map:weak_map(int,[]c0)`), a struct's
field (not a `<persistable>` one's), an element of a container, and a
module-scoped `var` (below). A module constant of it is an ordinary
constant (ch. 10's example `SavedInventories : weak_map(player, …) =
map{}` is a local of its test, by `bin/extract`).

**Module-scoped `var`** (`var X:t = e` at the top level or in a module):

1. Its type must be a `weak_map` (3502: `weak_map.versetest:16` `var
   Data:int = 0`, `GlobalVariables.versetest` 5, 39-44, 47; ch. 16 line 614;
   ch. 18 line 251).
2. Its key type must be a class with `<module_scoped_var_weak_map_key>`
   (3502: 26; ch. 3 line 1180).
3. When that class is `<persistent>`, the value type must be persistable
   (3502: 20; ch. 3 line 1202 with a `<persistent>` key; the API's `player`
   and `session`).
4. It is read and written one entry at a time: `X[k]`, `set X[k] = v`
   and paths through `X[k]`; the whole map is neither read nor replaced
   (3502: 168, 174; ch. 3 lines 1146-1176).
5. At most four `<persistent>`-keyed module-scoped `var weak_map`s, "Set
   to 4 for VerseTestScriptCmd" (the test runner's limit), and at the
   limit one of them must have a class value: 624 (three, valid), 631
   (four with `int` values: four 3502s, "Fail due to none of the value
   types being a class"), 639 (three `int`, one `class<final><persistable>`:
   valid), 648 and 657 (five, six: one 3502 each).
6. Effects: reading an entry is a read of mutable state (`<reads>`, the
   API's `ref` form is `<reads>`), writing one a write; rollback as any
   `var`.
7. The two class specifiers `<persistent>` and
   `<module_scoped_var_weak_map_key>` go on classes (`player`, `session`,
   every key class of the tests).

**Engine types.** `player`, `session`, `persistent_key`, `session_key`,
`Persistence.GetOrCreateKey`, `SetValid`, `Joined`, `Dropped`,
`RecordUpdates`, `TakeRecordedUpdates`, `Session.GetOrCreateKey`,
`Session.Reset`, `TestWeakMap` and `FitsInPlayerMap` are the engine's or
the test runner's; openverse has none of them (and `persistent_key` is not
in the API reference). The runtime error `WeakMapInvalidKey` is raised by
the engine for a key whose persistence is not valid (`player.IsActive`).

## Is weakness observable?

**No program in the Book's prose or tests observes an entry disappearing
because its key is no longer referenced.** Every case of
`weak_map.versetest`, `Map.versetest`, the chapters' examples and the API
reference was read for one. The closest are:

- The API reference's sentence that "a key can become absent on its own
  once nothing else holds it alive". No test or example shows it, and no
  program could: `W[K]` needs `K`, and while a program holds `K` the key is
  referenced.
- `weak_map.versetest` 675-688: after `Session.Reset()` the entry under
  `SessionKey1` is gone (`not SessionData[SessionKey1]`) **while the
  program still holds `SessionKey1`**. That is the engine ending a
  session's keys, not a collector dropping an unreachable key; and the case
  reads what the assertion at 675 wrote, in the runner's one program.
- 233-323, 330-353, 535-584: `WeakMapInvalidKey` runtime errors for
  `persistent_key`s the test runner makes invalid (`SetValid(false)`,
  `Dropped`). Again the program holds the key: it is the key's validity,
  set by the engine, not its reachability.

And none could, at the language level: a `weak_map` has no `Length`, no
iteration, no `comparable` (so no `=`), no conversion back to a map, and no
`ToString`; the only operation that reads it is `W[K]`, which needs a key
equal to the entry's. A key that is a value (an `int`, a `string`, a struct
of values) can always be built again, so an entry under it must never
disappear (the tests read `X[1]` of a `weak_map(int, int)` with nothing
holding `1`, 36-39, 138-153). A key that holds an object (a `<unique>`
class, compared by identity, or a struct or tuple holding one) is equal
only to keys holding that same object; once nothing reachable refers to
the object, no expression can produce a key equal to the entry's, and
the entry can never be read, whether it is there or not. An entry whose
value refers to its own key does not make the key reachable either, since
the value is reached only through the key (an ephemeron). So **"weak" is a
statement about storage, not about behaviour**, and at the language level
the Book's `weak_map` is exactly the entry-access subset of `map`, with
`map` below it, plus the module-scoped `var` rules. The only effect a
dropped entry could have is on memory: a program that fills a weak map with
entries under fresh objects needs less memory if the collector drops them,
and a resource limit is outside the semantics (openverse's C runtime has a
memory limit, Lean's interpreter none, [FORMAT.md](../FORMAT.md)).

**What openverse's collectors may do.** Neither implementation ever frees
an object: the object store is append-only (`Glob.heap` in Lean,
`objects.c` in C, where "a REF is an object's index, the address Lean
gives it"), and only the value heap of arrays, tuples and options is
reclaimed, by call ([DESIGN.md](../DESIGN.md#objects-in-the-c-runtime)). So
no key object ever becomes collectable, and nothing about an entry's key
lifetime arises. Dropping the entry of an unreachable key would need two
things neither runtime has: reachability of objects, and a way to tell a
weak map's array of pairs from any other array, a tag in the value
representation (`runtime/include/openverse.h`, which the QuickProof
theorems pin, and OVBC). Since no program can tell the difference,
openverse does not drop such entries: a `weak_map` is held exactly as a
`[k]v`. This is #491's "weak-key lifetime" answered by argument, not by
code; were the object store ever to reclaim objects, the rule a collector
may use is the one above: drop an entry whose key holds an object that is
unreachable from the roots other than through weak-map keys and the
values of entries so dropped, never one whose key is a value.

## Design

- **The type.** A front-end type `weak_map(k, v)` (`Ty.weakMap`), above
  `[k]v`, with a map's Verse Core representation, the array of its pairs:
  Verse Core, OVBC and the C runtime are unchanged. A conversion from a
  map or a weak map is a map's (the key and value converted, entry by
  entry, when their representations differ; nothing at all when they do
  not). The checks that a map's operations make are made on the weak map's
  key and value; the bulk operations refuse a `weak_map` with the Book's
  wording.
- **Entry operations** are a map's, written once for both: lookup, `set`
  of an entry and of a path through one, `op=`, and rollback, which is the
  `var`'s or the field's. A local `var` of the type may be replaced whole.
- **Module-scoped `var`.** The program's module state is one object of a
  hidden class, `$module_state`, whose `var` fields are the module-scoped
  variables. Every class without type parameters has a *prototype*, made
  by `Main`'s prelude before `Main` runs (#37), and Verse Core already
  types a reference literal to a prototype anywhere (`tc`'s `.lit (.ref a)`,
  `Sigs.protos`, `HeapOK`): the state is that prototype, so a use `X[k]`
  is `$module_state.X[k]` read through the literal, and `set X[k] = v` a
  write of the object's field in place. The prototype's fields start as
  their types' defaults, which for a `weak_map` is the empty map: the
  initializer must be `map{}` (every module-scoped `var` of the Book is).
  Rollback, effects (`<reads>`, `<writes>`) and the C runtime's object
  store are those of any object's `var` field. No Core change, no new
  primitive, no format change.

## As built

As designed ([LANGUAGE.md](../LANGUAGE.md#weak-maps),
[Module-scoped variables](../LANGUAGE.md#module-scoped-variables),
[DESIGN.md](../DESIGN.md#weak-maps-and-module-scoped-vars)): `Ty.weakMap`
in the front end's types, and `OpenVerse/Front/ModuleVars.lean`. Verse
Core, OVBC, the loader, the C runtime and every pinned file are unchanged,
and no theorem was touched. Two things came with it: a map, weak or not, is
read with a key of a class above or beside its key class at the class above
both (the API's `operator'()'(Map:[t]u, Key:t)` takes `t` above both;
`Map.versetest` 354, 388, 394), and a module-scoped `var` declared with no
value (`var x:int`, valid syntax in `Pointers.versetest:4`) parses and is
refused.

- **Tests.** `tests/verse/weak_map.verse` (covariance, lookups with keys of
  other classes, a generic function's value, struct values and paths, a
  class's fields, `comparable` keys, nested weak maps, options, rollback of
  a whole replacement and of entries), `weak_map_book.verse` (the Book's
  blocks 69, 70, 74, 76, a join and two meets), `module_var.verse` (the
  Book's ch. 17 example and block 75, rollback across two keys),
  `module_var_uses.verse` (two modules' vars of one name, `<suspends>`
  functions under `sync` and in a task, a refining cast's branches, a
  choice, a generic function, a `for` whose iterations fail, a class's
  methods); and 35 refusals, `tests/errors/weak_map_*` and `module_var_*`.
  Each expected output was derived by hand; Lean and C agree on each.
- **Fuzzing.** `scripts/fuzz-weakmap.sh` (`scripts/gen-weakmap.py`) gives
  a local, a module-scoped and a class field's weak map, each beside an
  ordinary map, one random stream of entry sets, `+=`, whole replacements,
  calls and failure contexts, nested and in `for`s, and prints every lookup
  of both after each statement; the Lean interpreter, `cverse` and the
  generator's model of the maps must print the same. 200 programs in the
  gate, 4,200 seeds checked; a model that does not undo failure contexts
  disagrees on 20 of 30.
- **The Book's tests** ([the survey's
  section](book-test-conformance.md#after-weak-maps-and-module-scoped-vars)):
  of `weak_map.versetest`'s 96 cases, 31 agree (18 on main), 12 are refused
  and 53 are not translatable; the `weak_map` cause of the survey is gone
  (23 cases: 18 agree, 1 not translatable, 4 under other causes).
- **Left.** `weak_map.versetest` 6, 624, 639, 667-669, the module-scoped
  `var`s whose key classes are `<allocates><computes>`, which openverse
  refuses as a class's effects (another cause, effects-of-classes); taken
  out, each agrees but 639, which needs a `<persistable>` class (#11). 41
  and 48 define `Main` with parameters; 32 writes a type alias in a body (a
  type as a value); `Map.versetest:401` sets through a key of a sibling
  class (VerseVM: a run-time failure; refused here, as the map's twin
  `:363`); 605, 611, 615 call `FitsInPlayerMap`, the persistence limit
  check. Module constants of `<unique>` classes (`GlobalVariables.versetest`
  72-74, `:decls`) need their initializers run once before `Main`: the
  module state can hold them, as `var` fields written by a function that
  `Main`'s prelude calls before `Main` (`PreludeOK` takes any function of
  `Main`'s signature), not built.
- **Not translatable** (53 cases): the engine's and the test runner's
  persistence (`Persistence.GetOrCreateKey`, `SetValid`, `Joined`,
  `Dropped`, `RecordUpdates`, `TakeRecordedUpdates`, `Session.Reset`,
  `persistent_key`, `session_key`, `TestWeakMap`, the runtime error
  `WeakMapInvalidKey`). A stand-in `persistent_key := class<unique><persistent><module_scoped_var_weak_map_key>{}`
  with a `GetOrCreateKey` would let them compile, not agree: each reads or
  writes under a key whose validity an earlier assertion set, or checks the
  update journal another assertion recorded, in the runner's one program,
  which the harness runs as separate programs. 261 and 267 alone would run,
  and they test only that `SetValid` and the writes succeed.

## Where the Book disagrees with itself

In the form of [the wiki
page](https://github.com/rudi-cilibrasi/openverse/wiki/Where-the-Book-disagrees-with-itself):

1. **The key of a module-scoped `var`: any class with the specifier, or
   a session or a player.**
   - *Prose* (ch. 18, `18_evolution.md:251`): "a persistent variable is a
     module-scoped `var` whose type is a `weak_map` keyed by a session or a
     player. A module-scoped `var` of any other type is rejected outright —
     the compiler asks for a "`session` or `player` key type"".
   - *Tests:* any class with `<module_scoped_var_weak_map_key>` keys one
     (`weak_map.versetest` 6, 624, 639, 667-669: `class1 := class<unique>…<persistent><module_scoped_var_weak_map_key>`),
     as ch. 3 says (`03_containers.md:1180`, "The key type must carry the
     `<module_scoped_var_weak_map_key>` specifier") and ch. 18's own
     example does with `persistent_key`.
   - *openverse:* follows the tests and ch. 3: a class with the specifier.
2. **A module-scoped `var` shown with a key class that lacks the
   specifier.**
   - *Prose:* ch. 16's block 15 (`16_modules.md:620-632`) and ch. 9's block
     05 (`09_structs_enums.md:95-107`) show `var GlobalCounter:weak_map(session, int)`
     and `var PlayerData : weak_map(player, player_stats)` at the left
     margin as the way to keep module state, with `session := class<unique>{}`
     and `player := class<concrete><unique>{}` in their hidden preludes.
   - *Tests:* a module-scoped `var` keyed by a class without
     `<module_scoped_var_weak_map_key>` is an error (`weak_map.versetest:26`,
     3502). The Book's own tool tests those two blocks with the `var` as a
     local of an `assert:` (`bin/extract` hoists only type definitions),
     where it is valid; the engine's `session` and `player` carry the
     specifier (the API reference).
   - *openverse:* follows the tests: at module scope such a `var` is
     refused, as a local it is accepted.
3. **Whether a module-scoped `var`'s values must persist when its key is
   not `<persistent>`.**
   - *Prose* (ch. 3, `03_containers.md:1180-1202`): "For module-scoped `var
     weak_map` variables, both key and value types have strict
     requirements. … The value type must be persistable."
   - *API reference* (`session`): "Unlike `player` it is not `<persistent>`,
     so values stored against it need not be persistable"; (`player`):
     "Because `player` is also `<persistent>`, a module-scoped `var
     weak_map` keyed on it must have a `persistable` value type".
   - *Tests:* only a `<persistent>` key with a value that does not persist
     (`weak_map.versetest:20`, 3502); none with another key.
   - *openverse:* follows the API reference, which the tests do not
     contradict: the values must persist when the key class is
     `<persistent>`.
