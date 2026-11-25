import OpenVerse.Front.Syntax

/-!
# A compound `set` whose right side replaces the place's container (#704)

`set X.p op= e`, with `p` a path of one or more steps (indices, keys,
struct fields, `?`) from a variable `X`, resolves its place before `e`
runs: the indices and keys, once, left to right, and with them the
container the last step writes into (`X` itself for one step, `X[i]` for
`X[i][j]`). Then `e` runs; then the old value is read from that container,
and the new one written into it.

When `e` only writes into the container (`set X[0] = …` for `set X[0] += e`,
`set S.F = …` for `set S.F += e`, or appends to it, `set X += …`), the
container is still the one `X` holds, so `e`'s writes are seen (the Book of
Verse's tests, `ArrayAppend.versetest` 140 and 183; Epic's VerseVM,
`compound-root-append.verse`). When `e` replaces the container itself, or a
container above it on the path, with a plain `set` (`set X = …` for
`set X[0] += e`), the old value is read from the container that was replaced
and the new one written into it: `X` keeps what `e` left. This is what Epic's VerseVM does (UEFN 43.12,
++Fortnite+Release-43.12-CL-60598086, "Use Verse VM": `var X:[][]int =
array{array{1, 2, 3}}`, `set X[0] += (if (set X = array{array{0}}; 0 = 0)
then array{42} else array{42})` leaves `X` as `array{array{0}}`,
`tests/conformance/versevm/compound-indexed-write.verse`), and what the
Book's VerseVM test `ArrayAppend.versetest` 12-15 expects. A whole variable,
`set X op= e`, is its own place: there `e`'s replacement is what is read
(`ArrayAppend.versetest` 8-10).

openverse's variables hold values, not mutable containers, so the identity
of the container is kept by a flag. For a local `var X`, every write that `e`
makes into `X` is written in `e` (Verse has no closures over variables), so
this pass, on the source, finds them. Where a plain one may replace the
container (its path is the container's path or a prefix of it: field names
equal, index and key steps compared when it runs), it becomes

    block:
        K₀ := …; …                     # its keys, once, in order
        if (not Lost?, the keys equal) { set Snap = X }
        V := set …                     # the write, at the bound keys
        if (the keys equal) { set Lost = true }
        V

so `Snap` is the variable as it was just before the container was first
replaced, and a write that a `break` leaves replaces nothing. The guarded
`set` becomes

    block:
        I₀ := …; …                    # the path's keys, once, in order
        var Lost:logic = false
        var Snap:t = X                 # t: X's written type
        set X.p' op= $placeGuard(e', Lost, Snap)

where `p'` is `p` with the keys bound. The elaborator (`elabSetWith`)
reads a guarded place from `Snap`, the variable as it was when its
container was replaced, when `Lost` holds, and then leaves `X` as it is.
A failure undoes `Lost` and `Snap` with every other write (they are
variables), and the names are hidden ones (`$place…`).

Only local `var`s are guarded here. A path through an object resolves the
object before `e` (#34), and past the object's field `e` can replace a
container through a call, another reference to the object or another task,
which no pass over the source sees: the elaborator watches those through the
object itself (`PlaceWatch`, `elabSetWith`'s `watchPush` and `watchWrites`),
also for module-scoped variables, the fields of the module state's object.
-/

namespace OpenVerse.Front.CompoundPlaces

/-- The marker of a guarded `set`'s right side: `$placeGuard(e, Lost, Snap)`. -/
def guardName : String := "$placeGuard"

/-- A step of a place: a field, `?`, or an index's keys. -/
inductive Step where
  | field (name : String)
  | query
  | index (keys : List SExpr)

/-- A place `X.s₁…sₙ` taken apart: its root's name and its steps. -/
partial def path? : SExpr → Option (String × List Step)
  | .ident _ n => some (n, [])
  | .member _ e f => (path? e).map fun (n, ss) => (n, ss ++ [.field f])
  | .query _ e => (path? e).map fun (n, ss) => (n, ss ++ [.query])
  | .app _ e ks true => (path? e).map fun (n, ss) => (n, ss ++ [.index ks])
  | _ => none

/-- The test that keys `k` and `j` are equal: `none` when they are literals
    that differ, `some none` when they are the same literal. -/
def keyTest (p : Pos) (k j : SExpr) : Option (Option SExpr) :=
  match k, j with
  | .int _ a, .int _ b | .char _ a, .char _ b | .char32 _ a, .char32 _ b =>
    if a == b then some none else none
  | k, j => some (some (.cmp p k [("=", j)]))

/-- Whether a write at `q` may replace the container at `c`, and the tests,
    run when it is about to, that it does: `q` is `c` or a prefix of it,
    step by step of the same kind (the same field, `?`, or an index whose
    keys are equal, `keyTest`). -/
def covers (p : Pos) (q c : List Step) : Option (List SExpr) := do
  if q.length > c.length then none
  let tests ← (q.zip c).mapM fun (s : Step × Step) => match s with
    | (.field f, .field g) => if f == g then some [] else none
    | (.query, .query) => some []
    | (.index ks, .index js) => do
      if ks.length != js.length then none
      let tests ← (ks.zip js).mapM fun (k, j) => keyTest p k j
      return tests.filterMap id
    | _ => none
  return tests.flatten

/-- A key that is bound to a name of its own: not a literal. -/
def bindsKey : SExpr → Bool
  | .int .. | .char .. | .char32 .. => false
  | _ => true

/-- A place's keys bound to names `pfx0`, `pfx1`, …, in order (literals kept):
    the bindings, and the place with the names in their keys' places. -/
partial def bindKeys (pfx : String) (l : SExpr) : List SExpr × SExpr :=
  let rec go (n : Nat) : SExpr → List SExpr × SExpr × Nat
    | .app q base ks true =>
      let (h, base', n) := go n base
      let (h, ks', n) := ks.foldl (fun (h, acc, n) k =>
        if bindsKey k then (h ++ [.decl q s!"{pfx}{n}" none false k], acc ++ [.ident q s!"{pfx}{n}"], n + 1)
        else (h, acc ++ [k], n)) (h, [], n)
      (h, .app q base' ks' true, n)
    | .member q base f => let (h, base', n) := go n base; (h, .member q base' f, n)
    | .query q base => let (h, base', n) := go n base; (h, .query q base', n)
    | e => ([], e, n)
  let (h, l', _) := go 0 l
  (h, l')

/-- A guarded place: its root, the steps of its container (keys bound), the
    prefix of its hidden names, and the names of its flag and snapshot. -/
structure Guard where
  root : String
  container : List Step
  tag : String
  lost : String
  snap : String

/-- Whether a `set` written at `l` may replace `g`'s container (`covers`). -/
def mayReplace (g : Guard) (p : Pos) (l : SExpr) : Bool :=
  match path? l with
  | some (n, ss) => n == g.root && (covers p ss g.container).isSome
  | none => false

/-- Whether a `set` in `e` may replace `g`'s container: a plain one. A
    compound one, `set X += …` of an array (the only `op=` of a container),
    appends in place, as Epic's VerseVM does (`compound-root-append.verse`). -/
partial def replaces (g : Guard) (e : SExpr) : Bool :=
  (match e with
    | .set p l none _ => mayReplace g p l
    | _ => false) || e.children.any (replaces g)

/-- `body` when every one of `conds` succeeds (all of them none: always). -/
def whenAll (q : Pos) (conds : List SExpr) (body : SExpr) : SExpr :=
  if conds.isEmpty then body else .ite q conds (.block q [body]) none

/-- `e` with each `set` that may replace `g`'s container instrumented: when
    its keys are the container's, the variable as it is before the write
    (`Snap`, unless the container was replaced already), and after the
    write, that the container was replaced (`Lost`; not when the write is
    left by a `break`). The write's keys are bound first, as `set`
    evaluates them before its value; its value stays the code's. -/
partial def instrument (g : Guard) (e : SExpr) : SExpr :=
  match e with
  | .set q l none r =>
    if !mayReplace g q l then Id.run (e.mapChildrenM fun c => pure (instrument g c)) else
    let pfx := s!"{g.tag}_w{q.line}_{q.col}"
    let (keys, l') := bindKeys s!"{pfx}_k" l
    let tests := ((path? l').bind fun (_, ss) => covers q ss g.container).getD []
    let snapshot := whenAll q (.notE q (.query q (.ident q g.lost)) :: tests)
      (.set q (.ident q g.snap) none (.ident q g.root))
    let replaced := whenAll q tests (.set q (.ident q g.lost) none (.ident q "true"))
    .block q (keys.map (instrument g) ++ [snapshot,
      .decl q s!"{pfx}_v" none false (.set q l' none (instrument g r)), replaced, .ident q s!"{pfx}_v"])
  | e => Id.run (e.mapChildrenM fun c => pure (instrument g c))

/-- The local `var`s that code declares, each with its written type when
    every declaration of it writes the same one. -/
partial def localVars (e : SExpr) : List (String × Option STy) :=
  let rec decls : SExpr → List (String × Option STy)
    | .decl _ n t true x => (n, t) :: decls x
    | e => e.children.flatMap decls
  let all := decls e
  all.map (·.1) |>.eraseDups |>.map fun n =>
    let tys := (all.filter (·.1 == n)).map (·.2)
    (n, if tys.all (· == tys.head!) then tys.head! else none)

/-- A compound `set` of `vars`' place whose right side may replace its
    container, guarded (see the module's comment); anything else as it is. -/
def guardSet (vars : List (String × Option STy)) : SExpr → SExpr
  | e@(.set p l (some op) r) =>
    if p.line == 0 then e else
    match path? l with
    | some (root, ss@(_ :: _)) =>
      match vars.lookup root with
      | none => e
      | some ty =>
        let tag := s!"$place{p.line}_{p.col}"
        let (keys, l') := bindKeys s!"{tag}_i" l
        let ss' := ((path? l').map (·.2)).getD ss
        let g : Guard := { root, container := ss'.dropLast, tag, lost := s!"{tag}_lost", snap := s!"{tag}_snap" }
        if !replaces g r then e else
        .block p (keys ++ [
          .decl p g.lost (some (.name "logic")) true (.ident p "false"),
          .decl p g.snap ty true (.ident p root),
          .set p l' (some op) (.app p (.ident p guardName) [instrument g r, .ident p g.lost, .ident p g.snap] false)])
    | _ => e
  | e => e

/-- Code with its guarded compound `set`s (`guardSet`), the innermost first. -/
def guardCode (e : SExpr) : SExpr :=
  let vars := localVars e
  if vars.isEmpty then e else e.mapAll id (guardSet vars)

/-- A definition with the compound `set`s of its code guarded: each
    function's body, method's body and default on its own. -/
partial def guardTop : STop → STop
  | .fn p n ps tps specs r b =>
    .fn p n (ps.map fun q => { q with default := q.default.map guardCode }) tps specs r (guardCode b)
  | .const p n specs t v => .const p n specs t (guardCode v)
  | .classDef p n ns tps specs ps isI fs ms =>
    .classDef p n ns tps specs ps isI (fs.map fun f => { f with default := f.default.map guardCode })
      (ms.map guardTop)

/-- The program with its compound `set`s guarded (`guardSet`). -/
def desugar (tops : List STop) : List STop := tops.map guardTop

end OpenVerse.Front.CompoundPlaces
