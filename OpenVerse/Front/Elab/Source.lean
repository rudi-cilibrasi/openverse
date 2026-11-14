/- Elaboration of a program's source, before its classes and types (phases 1–3 of
   `elabProgramCore`); public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Lowering
import OpenVerse.Front.InitializerConvergence
import OpenVerse.Front.Aliases
import OpenVerse.Front.BuiltinValues
import OpenVerse.Front.FinalSuper
import OpenVerse.Front.Bitwise
import OpenVerse.Front.TypeValues
import OpenVerse.Front.TypeArguments

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
  /-- The places of the filters of every `for` as written (`forFilterPositions`). -/
  forFilters : List Pos := []
  /-- The type aliases, each by its name, written out (`Aliases.expand`). -/
  aliases : List (String × Aliases.Alias) := []

/-- Each name is defined once in its scope, the top level or a module: only
    functions of one scope share a name, as its overloads. A class, an
    interface, a struct, an enum, a constant and a function of one name are
    two definitions of it (two modules of one name, and a module and a
    definition, are `resolveModules`' to refuse). -/
def checkDefinedOnce (tops : List STop) : Except String Unit := do
  -- (each qualified name seen, and whether only functions have it so far)
  let mut seen : Std.HashMap String Bool := {}
  for t in tops do
    let (p, n, isFn) := match t with
      | .fn p n .. => (p, n, true)
      | .const p n .. | .classDef p n .. => (p, n, false)
    -- (not the parser's markers, `$module:…`, nor the compiler's names)
    if (qualParts n).any (·.startsWith "$") then continue
    if let some onlyFns := seen[n]? then
      if !(isFn && onlyFns) then
        throw s!"{p.show}: '{".".intercalate (qualParts n)}' is defined twice (only functions can be overloaded)"
    seen := seen.insert n isFn

/-- No definition takes the name of a definition of a scope around it
    (Book of Verse ch. 10, "Shadowing and Qualification": "you cannot
    redefine names that already exist in an enclosing scope"; the rule is
    pinned in docs/research/qualified-names.md, "Shadowing"), whichever is
    written first: a module's member or a module, named like a definition
    of a module around it or of the top level; a class's or an interface's
    member, an enum's value or a struct's field, named like a definition of
    the scope the type is defined in or of one around it (the type itself
    included); a function's parameter, likewise. Functions overload across
    scopes as in one (Book of Verse tests, `Overloading.versetest`, "Test
    overloading a function across different scopes"): a function or method
    and a function around it of its name are returned, for
    `checkSignatures` to require that no call fits both, and a parameter of
    a function type may take an enclosing function's name. A qualified
    definition, `(M:)x`, `(c:)m`, `(e:)v`, `(local:)X`, says where it is,
    and may; an override implements an inherited member and is none; the
    entry point `Main`, which the Book does not have, shadows nothing.
    Locals are checked where names are resolved (`resolveModules`, the
    elaborator). -/
def checkNoShadowing (tops : List STop) : Except String (List ScopePair) := do
  let shown (ps : List String) : String := ".".intercalate ps
  -- (definitions written `(M:)x` in their module)
  let qualified : List String := tops.filterMap fun
    | .const _ n _ _ _ => (qualMarker? n).map (·.1)
    | _ => none
  -- the definitions of the top level and the modules: each one's scope, name,
  -- what it is and where
  let kind : STop → String
    | .fn .. => "function"
    | .classDef _ _ _ _ _ _ isI .. => if isI then "interface" else "class"
    | .const _ _ _ _ (.structDef ..) => "struct"
    | .const _ _ _ _ (.enumDef ..) => "enum"
    | .const _ _ _ _ (.refineDef ..) | .const _ _ _ _ (.typeAlias ..) => "type"
    | .const .. => "constant"
  let defs : List (List String × String × String × Pos) := tops.filterMap fun t =>
    let (p, n) := match t with
      | .fn p n .. | .const p n .. | .classDef p n .. => (p, n)
    if let some m := moduleMarker? n then
      let ps := qualParts m
      some (ps.dropLast, ps.getLastD "", "module", p)
    else
      let ps := qualParts n
      if ps.any (·.startsWith "$") || n == "Main" then none else some (ps.dropLast, ps.getLastD n, kind t, p)
  -- the definitions a scope `sc`, or one around it (`within`: `sc` itself
  -- too), has of name `x`
  let outers (sc : List String) (within : Bool) (x : String) : List (List String × String × String × Pos) :=
    defs.filter fun (s, y, _, _) => y == x && s.length ≤ sc.length && sc.take s.length == s &&
      (within || s.length < sc.length)
  let message (p : Pos) (what x whr qual : String) : List String × String × String × Pos → String
    | (s, _, k, q) =>
      s!"{p.show}: {what} '{x}'{whr} has the name of the {k} {shown (s ++ [x])} ({q.show}): Verse does not allow shadowing (Book of Verse ch. 10); rename one, or qualify this one, ({qual}:){x}"
  let refuse (p : Pos) (what x whr qual : String) (os : List (List String × String × String × Pos)) : Except String Unit :=
    match os.head? with
    | some o => throw (message p what x whr qual o)
    | none => pure ()
  let mut pairs : Array ScopePair := #[]
  -- a function or method `inner`: refused beside a definition around it
  -- that is no function, else paired with each function around it
  let fnOuters (p : Pos) (what x whr qual inner : String) (os : List (List String × String × String × Pos)) :
      Except String (List ScopePair) := do
    refuse p what x whr qual (os.filter (·.2.2.1 != "function"))
    return os.map fun (s, _, _, q) => { pos := p, inner, outer := qualJoin (s ++ [x]), outerPos := q, qualifier := qual }
  let params (sc : List String) (p : Pos) (owner : String) (ps : List SParam) : Except String Unit :=
    ps.forM fun prm =>
      if prm.name.isEmpty || prm.name.startsWith "$" || prm.name.startsWith "(" then pure ()
      else
        let os := outers sc true prm.name
        -- (a parameter of a function type overloads as a function does)
        let os : List (List String × String × String × Pos) := match prm.ty with
          | .fn .. => os.filter fun (_, _, k, _) => k != "function"
          | _ => os
        match prm.named, os.head? with
        -- (a named parameter, which no qualifier may name: its name is how a
        -- call gives it)
        | true, some (s, _, k, q) =>
          throw s!"{p.show}: the named parameter '?{prm.name}' of {owner} has the name of the {k} {shown (s ++ [prm.name])} ({q.show}): Verse does not allow shadowing (Book of Verse ch. 10); rename one"
        | _, _ => refuse p "the parameter" prm.name s!" of {owner}" "local" os
  for t in tops do
    match t with
    | .fn p n ps .. =>
      let parts := qualParts n
      if parts.any (·.startsWith "$") then continue
      if !qualified.contains n then
        let x := parts.getLastD n
        pairs := pairs ++ (← fnOuters p "the function" x "" (shown parts.dropLast) n (outers parts.dropLast false x))
      params parts.dropLast p (shown parts) ps
    | .const p n _ _ body =>
      let parts := qualParts n
      if let some m := moduleMarker? n then
        let mp := qualParts m
        if !qualified.contains (qualJoin mp) then
          refuse p "the module" (mp.getLastD "") "" (shown mp.dropLast) (outers mp.dropLast false (mp.getLastD ""))
        continue
      if parts.any (·.startsWith "$") then continue
      let sc := parts.dropLast
      let x := parts.getLastD n
      if !qualified.contains n then refuse p s!"the {kind t}" x "" (shown sc) (outers sc false x)
      -- (an enum's values and a struct's fields, which a qualifier may name)
      match body with
      | .enumDef _ vs _ =>
        for v in vs do
          if !v.startsWith "(" then refuse p "the value" v s!" of {shown parts}" x (outers sc true v)
      | .structDef _ _ _ fs =>
        for ⟨f, _, _, _, _, _⟩ in fs do
          if !f.startsWith "(" then refuse p "the field" f s!" of {shown parts}" x (outers sc true f)
      | _ => pure ()
    | .classDef p n _ _ _ _ isI fields methods =>
      let parts := qualParts n
      let sc := parts.dropLast
      let x := parts.getLastD n
      if !qualified.contains n then
        refuse p s!"the {if isI then "interface" else "class"}" x "" (shown sc) (outers sc false x)
      for fd in fields do
        if !fd.name.startsWith "(" && !fd.isOverride then
          refuse p "the field" fd.name s!" of {shown parts}" x (outers sc true fd.name)

      for m in methods do
        if let .fn mp mn mps _ effs .. := m then
          if !mn.startsWith "(" && !mn.startsWith "$" && !effs.contains "override" then
            pairs := pairs ++ (← fnOuters mp "the method" mn s!" of {shown parts}" x s!"{n}.{mn}" (outers sc true mn))
          params sc mp s!"{shown parts}.{bareName mn}" mps
  return pairs.toList

/-- The constants of a program, modules resolved, in the order written: each
    with the constants its value names. -/
partial def constantUses (tops : List STop) : List (Pos × String × List String) :=
  let consts : List (Pos × String × SExpr) := tops.filterMap fun
    | .const _ _ _ _ (.structDef ..) | .const _ _ _ _ (.enumDef ..) | .const _ _ _ _ (.refineDef ..) => none
    | .const p n _ _ e => if (qualParts n).any (·.startsWith "$") then none else some (p, n, e)
    | _ => none
  let names : Std.HashSet String := Std.HashSet.ofList (consts.map (·.2.1))
  let rec uses : SExpr → List String
    | .ident _ n => if names.contains n then [n] else []
    | e => e.children.flatMap uses
  consts.map fun (p, n, e) => (p, n, (uses e).eraseDups)

/-- A constant's value is computed from the constants it names, so none may
    name itself, directly or through others (`X:int = X`, or `I:int = J` and
    `J:int = I`): its computation would never end (as a field default that
    depends on itself, which the elaboration of defaults refuses). (One
    defined after it in its own scope is refused too, `checkConstantOrder`.) -/
def checkConstantCycles (tops : List STop) : Except String Unit := do
  let graph := constantUses tops
  let shown (n : String) : String := ".".intercalate (qualParts n)
  for (p, n, _) in graph do
    -- (a path from `n` back to it, breadth first)
    let mut seen : List String := []
    let mut todo : List (String × List String) := [(n, [])]
    while !todo.isEmpty do
      let (m, path) := todo.head!
      todo := todo.tail!
      for u in ((graph.find? (·.2.1 == m)).map (·.2.2)).getD [] do
        if u == n then
          let via := (path ++ [m]).drop 1
          throw s!"{p.show}: the value of the constant {shown n} depends on itself{if via.isEmpty then "" else s!" (through {", ".intercalate (via.map shown)})"}"
        if !seen.contains u then
          seen := u :: seen
          todo := todo ++ [(u, path ++ [m])]

/-- A constant's value may name a constant of its own scope (a module, or the
    top level) only when that one is defined before it, in the same file: the
    Book of Verse's tests, `Features/DefaultValueAssignment.versetest` 102 and
    128 ("module variable initializers can't refer to module variables that
    succeed them in the same module"), refuse one defined after it, and allow
    one of another module or of an enclosing scope, defined before or after
    (`c22`). (One that depends on itself is `checkConstantCycles`'s.) -/
def checkConstantOrder (tops : List STop) : Except String Unit := do
  let graph := constantUses tops
  let shown (n : String) : String := ".".intercalate (qualParts n)
  let scope (n : String) : List String := (qualParts n).dropLast
  for ((p, n, uses), i) in graph.zipIdx do
    for u in uses do
      if let some j := graph.findIdx? (·.2.1 == u) then
        let q := graph[j]!.1
        if j > i && scope u == scope n && q.file == p.file then
          throw s!"{p.show}: the value of the constant {shown n} names {shown u}, which is defined after it in the same scope ({q.show}): a constant may only use one defined before it (Book of Verse's tests, DefaultValueAssignment.versetest)"

/-- A type of the program's own does not take a built-in type's name. -/
def checkTypeNames (tops : List STop) : Except String Unit := do
  for t in tops do
    match t with
    | .const p n _ _ (.structDef ..) | .const p n _ _ (.enumDef ..) | .classDef p n .. =>
      if ("char32" :: typeNames).contains n then throw s!"{p.show}: {n} is a built-in type"
    | _ => pure ()

/-- No definition takes a reserved name (`reservedNames`), at any scope. -/
def checkReservedNames (tops : List STop) : Except String Unit := do
  for t in tops do
    for (p, n) in t.definedNames do
      let n := (n.splitOn "::").getLast?.getD n
      -- (an extension method's, `M` of its function `$ext:M`)
      let n := (extensionMethod? n).getD n
      if reservedNames.contains n then throw s!"{p.show}: '{n}' is reserved: no definition can take it"

mutual
/-- `checkDefers` in an expression. -/
partial def checkDefersIn : SExpr → Except String Unit
  | .block _ es => checkDefersSeq es
  -- (an `if`'s or a `for`'s clauses are a sequence too, whose value is the
  -- last one's)
  | .ite _ cs t e => do checkDefersSeq cs; checkDefersIn t; e.forM checkDefersIn
  | .forE _ cs b => do checkDefersSeq cs; checkDefersIn b
  | .app p (.ident _ "$defer") _ _ =>
    throw s!"{p.show}: defer: is a statement: it has no value, so it cannot end a block or be where a value is taken (Book of Verse ch. 7)"
  | e => e.children.forM checkDefersIn

/-- `checkDefers` in a sequence: a defer with code after it is a statement,
    whose body is checked. -/
partial def checkDefersSeq (es : List SExpr) : Except String Unit := do
  for (e, i) in es.zipIdx do
    match e with
    | .app _ (.ident _ "$defer") args _ => if i + 1 < es.length then args.forM checkDefersIn else checkDefersIn e
    | e => checkDefersIn e
end

/-- A `defer:` is a statement of a block, with code after it in the block
    (Book of Verse ch. 7: it "cannot be used in positions where a value is
    expected"): not a block's last, whose value is the block's, nor an operand
    (`A and defer{…}`), a branch or a body of its own. -/
def checkDefers (tops : List STop) : Except String Unit :=
  tops.forM (·.code.forM checkDefersIn)

/-- A literal value, which neither fails nor has several values. -/
partial def SExpr.isLiteral : SExpr → Bool
  | .int .. | .char .. | .char32 .. | .float .. => true
  | .str _ parts => parts.all fun | .text _ => true | .code _ => false
  | .ident _ n => n == "true" || n == "false"
  | .tuple _ es | .arrayLit _ es => es.all SExpr.isLiteral
  | .mapLit _ kvs => kvs.all fun (k, v) => k.isLiteral && v.isLiteral
  | _ => false

/-- A `for` with no generator runs its body at most once, when its clauses
    succeed (Book of Verse ch. 7, "For Without a Generator"): clauses that
    cannot fail, no clause at all, or literals and bindings of literals
    (`for(X := array{1, 2})` for `for(X : array{1, 2})`, `for(1)`), are
    refused, as the Book's tests do ("Not an iterable"); and so is a filter
    that is a literal, which cannot fail ("Filters must be failable", ch. 7;
    `for.versetest:223`). -/
partial def checkForClauses (tops : List STop) : Except String Unit := do
  let literalClause : SExpr → Bool
    | .decl _ _ _ false v => v.isLiteral
    | c => c.isLiteral
  let rec go : SExpr → Except String Unit
    | .forE p cs b => do
      if cs.all literalClause then
        throw s!"{p.show}: this for has no generator (X : A, or X := A..B) and its clauses cannot fail, so it would run its body once: write X : A to iterate over A (Book of Verse ch. 7)"
      -- (a filter that is a literal cannot fail: "Filters must be
      -- failable", Book of Verse ch. 7, and its tests, for.versetest:223)
      if let some c := cs.find? SExpr.isLiteral then
        throw s!"{c.pos.show}: this filter of a for is a literal, which cannot fail: a filter must be able to fail (Book of Verse ch. 7, \"Filters must be failable\")"
      cs.forM go; go b
    | .structDef _ _ _ fs => fs.forM fun f => f.default.forM go
    | e => e.children.forM go
  tops.forM (·.code.forM go)

/-- The places of the filters of every `for` as written: each clause that
    is neither a generator (`X : A`, `X := A..B`) nor a definition (`X := e`,
    `X:t = e`, `var X:t = e`), and has no choice in it and calls no function
    with several values, which make it a generator over their values (#208,
    #283). The elaboration checks that each can fail (`Ctx.forFilters`,
    Book of Verse ch. 7: "Each filter must be failable"); a clause that
    inlining or a choice's preparation adds, as the statements of a function
    with several values that a `for` takes, is none of them. -/
partial def forFilterPositions (tops : List STop) : List Pos :=
  let mv := Choice.multiValued (Choice.multiCandidates tops)
  let callsMulti (c : SExpr) : Bool :=
    Choice.anyE (fun | .app _ (.ident _ f) _ _ => mv.contains f | _ => false) c
  let rec go : SExpr → List Pos
    | .forE _ cs b =>
      (cs.filterMap fun c => match c with
        | .gen .. | .decl .. => none
        | c => if Choice.hasChoice [c] || callsMulti c then none else some c.pos) ++
      cs.flatMap go ++ go b
    | e => e.children.flatMap go
  tops.flatMap fun t => t.code.flatMap go

/-- The code of a `spawn` cannot leave it: no `return`, and no `break` but
    of a loop inside it (Book of Verse tests, `SpawnAndTask.versetest` 876-892:
    "Can't break or return from a spawn", 3551). -/
partial def checkSpawnExits (tops : List STop) : Except String Unit := do
  let refuse (p : Pos) (what : String) : Except String Unit :=
    throw s!"{p.show}: a {what} inside spawn would leave it: the spawned call runs as a task of its own (Book of Verse tests, SpawnAndTask.versetest)"
  -- (`inLoop`: inside a loop of the spawn's own code)
  let rec inSpawn (inLoop : Bool) : SExpr → Except String Unit
    | .ret p _ => refuse p "return"
    | .brk p => if inLoop then pure () else refuse p "break"
    | .loop _ b => inSpawn true b
    | .structDef .. => pure ()
    | e => e.children.forM (inSpawn inLoop)
  let rec go : SExpr → Except String Unit
    | .app _ (.ident _ "$spawn") [b] false => inSpawn false b
    | .structDef _ _ _ fs => fs.forM fun f => f.default.forM go
    | e => e.children.forM go
  tops.forM (·.code.forM go)

/-- A `loop` that nothing leaves, no `break` of its own and no `return`, in
    a function that cannot suspend, would run until the program's fuel is
    spent: refused, as the Book's tests do ("Ensure loop is not empty",
    "Ensure loop has matching break", `FlowControl/Break.versetest` 117,
    160, 3579). A `<suspends>` function's loop may wait forever, as a game's
    loop does (`Break.versetest:17-29`). -/
partial def checkLoopExits (tops : List STop) : Except String Unit := do
  -- (`own`: a `break` here leaves the loop being checked)
  let rec exits (own : Bool) : SExpr → Bool
    | .ret .. => true
    | .brk _ => own
    | .loop _ b => exits false b
    | .structDef .. => false
    | e => e.children.any (exits own)
  let rec go : SExpr → Except String Unit
    | .loop p b => do
      if !exits true b then
        throw s!"{p.show}: nothing leaves this loop, no break of its own and no return, so it would run forever: a loop of a function that cannot suspend needs a way out (Book of Verse tests, Break.versetest)"
      go b
    | .structDef _ _ _ fs => fs.forM fun f => f.default.forM go
    | e => e.children.forM go
  -- (the code of each function and method that cannot suspend)
  let rec unsuspending : STop → List SExpr
    | t@(.fn _ _ _ _ effs _ _) => if effs.contains "suspends" then [] else t.code
    | .classDef _ _ _ _ _ _ _ _ ms => ms.flatMap unsuspending
    | _ => []
  tops.forM fun t => (unsuspending t).forM go

/-- `(super:)M` calls the implementation above of the method it is in: it
    is written only in the code of an `<override>` method named `M` (its
    body, a block or a `spawn` in it, its parameters' defaults), not in
    another method, a class's `block:`, a field's default or a function
    (the Book's tests, `Super.versetest`: "super on another method", `:192`,
    "Calling `(super:)` from blocks is not allowed", `:237`, a function's,
    `:204`, 3612; ch. 6: "The `(super:)` syntax for calling parent class
    methods **cannot** be used in nested functions"; a `spawn` in the
    override may, `SOL-9691-CaptureSuper.versetest`). An overload of `M`
    above is any of them (`Super.versetest:54`). -/
partial def checkSuperCalls (tops : List STop) : Except String Unit := do
  -- (`inM`: the method whose override the code is in, its name without a
  -- qualifier)
  let rec go (inM : Option String) : SExpr → Except String Unit
    | .member p (.ident _ "(super:)") m =>
      if inM == some m then pure () else
        throw s!"{p.show}: (super:){m} is not in an override of {m}: (super:) calls the implementation above of the method it is in, from that method's own code (Book of Verse tests, Super.versetest: \"super on another method\", \"Calling `(super:)` from blocks is not allowed\")"
    | .structDef _ _ _ fs => fs.forM fun f => f.default.forM (go none)
    | e => e.children.forM (go inM)
  let unqualified (n : String) : String :=
    if n.startsWith "(" then ((n.splitOn ":)").drop 1).headD n else n
  for t in tops do
    match t with
    | .classDef _ _ _ _ _ _ _ fs ms =>
      fs.forM fun f => f.default.forM (go none)
      for m in ms do
        match m with
        | .fn _ n _ _ specs _ _ =>
          let inM := if n != "$block" && specs.contains "override" then some (unqualified n) else none
          m.code.forM (go inM)
        | m => m.code.forM (go none)
    | t => t.code.forM (go none)

/-- Five forms the Book's tests refuse, each where the source shows it
    (`type-checks-other` of the [map](../../docs/research/book-test-conformance.md)):
    a default on a positional parameter, `F(X:int=0)` ("Named parameters with
    default values are truly optional", ch. 6;
    `2023-01-18-FunctionParameterWithoutDomain.versetest:12`, 3625); a named
    argument before a positional one (ch. 6: "Invalid: named arg before
    positional"; `DefaultNamed.versetest:122`, 3629); a `var` field in a
    struct ("Structs cannot contain pointers", `Classes/Struct.versetest:31`,
    3607); a `return` or `break` that leaves a construction's field value
    (`Classes/Constructor.versetest:528`, 3626); and `option{}` with nothing
    in it (`Option.versetest:94`, 3622). -/
partial def checkBookForms (tops : List STop) : Except String Unit := do
  -- (a jump out of a construction's field value: `inLoop`, inside a loop
  -- of the value's own code)
  let rec jumps (inLoop : Bool) : SExpr → Except String Unit
    | .ret p _ => throw s!"{p.show}: a return cannot leave a construction's field value (Book of Verse tests, Classes/Constructor.versetest)"
    | .brk p => if inLoop then pure () else
        throw s!"{p.show}: a break cannot leave a construction's field value (Book of Verse tests, Classes/Constructor.versetest)"
    | .loop _ b => jumps true b
    | .structDef .. => pure ()
    | e => e.children.forM (jumps inLoop)
  let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
  let rec go : SExpr → Except String Unit
    | .optionLit p (.block _ []) =>
      throw s!"{p.show}: option\{} has no value: write option\{e}, or false for an empty option (Book of Verse tests, Option.versetest)"
    | .construct p n ts fs => do
      for f in fs do
        match f with
        | .decl _ _ _ _ v => jumps false v
        | _ => pure ()
      (SExpr.construct p n ts fs).children.forM go
    | .structDef p _ _ fs => do
      if let some f := fs.find? (·.isVar) then
        throw s!"{p.show}: a struct's field is no var: '{f.name}' (a struct is a value; Book of Verse tests, Classes/Struct.versetest)"
      fs.forM fun f => f.default.forM go
    | e@(.app _ f args _) => do
      let isMarker := match f with | .ident _ n => n.startsWith "$" | _ => false
      if !isMarker then
        if let some k := args.findIdx? isNamed then
          if let some a := (args.drop (k + 1)).find? (!isNamed ·) then
            throw s!"{a.pos.show}: a positional argument after a named one: the named arguments come last (Book of Verse ch. 6, \"Invalid: named arg before positional\")"
      e.children.forM go
    | e => e.children.forM go
  -- (a parameter with a default is named: of each function and method)
  let rec params : STop → Except String Unit
    | .fn p n ps .. => do
      unless n.startsWith "$" do
        if let some q := ps.find? (fun q => !q.named && q.default.isSome) then
          throw s!"{p.show}: {q.name} has a default but is not named: only a named parameter has one, ?{q.name}:t = e (Book of Verse ch. 6, and its tests, 2023-01-18-FunctionParameterWithoutDomain.versetest)"
    | .classDef _ _ _ _ _ _ _ _ ms => ms.forM params
    | _ => pure ()
  for t in tops do
    params t
    match t with
    -- (a struct defined at the top is its own node, for its fields' var)
    | .const _ _ _ _ s@(.structDef ..) => go s
    | t => t.code.forM go

/-- A `profile` block is code of a function's, not of an initializer: none
    in a constant's value or a field's default (Book of Verse tests,
    profile_simple.versetest:144, "Cannot use profiles inside initializers -
    only allowed inside control-blocks", 3675). -/
def checkProfiles (tops : List STop) : Except String Unit := do
  let profile? : SExpr → Option SExpr :=
    Refine.findPart (fun | .decl _ n .. => n.startsWith profilePrefix | _ => false) false
  let refuse (p : Pos) (what : String) : Except String Unit :=
    throw s!"{p.show}: profile is not allowed in {what}: an initializer; it measures code of a function's (Book of Verse tests, profile_simple.versetest)"
  for t in tops do
    match t with
    | .const _ _ _ _ (.structDef _ _ _ fs) | .classDef _ _ _ _ _ _ _ fs _ =>
      for f in fs do
        if let some r := f.default.bind profile? then refuse r.pos s!"the default of '{f.name}'"
    | .const _ n _ _ e =>
      if let some r := profile? e then refuse r.pos s!"the value of {n}"
    | .fn .. => pure ()

/-- `return` leaves a function's body, so it is refused where there is none: in
    a constant's value, and in a field's default, which is evaluated where an
    object is constructed and would leave the function that constructs it. -/
def checkReturns (tops : List STop) : Except String Unit := do
  let ret? : SExpr → Option SExpr := Refine.findPart (fun | .ret .. => true | _ => false) false
  for t in tops do
    match t with
    | .const _ n _ _ (.structDef _ _ _ fs) | .classDef _ n _ _ _ _ _ fs _ =>
      for ⟨f, _, d, _, _, _⟩ in fs do
        if let some r := d.bind ret? then
          throw s!"{r.pos.show}: return is not allowed in a field's default (of '{f}' in {n})"
    | .const _ n _ _ e =>
      if let some r := ret? e then
        throw s!"{r.pos.show}: return is not allowed in a constant's value (of {n}), which is in no function"
    | .fn .. => pure ()

mutual
/-- `checkNestedReturns`: code whose value is not returned. -/
partial def nestedReturnsFree : SExpr → Except String Unit
  | .ret _ (some e) => nestedReturnsResult e
  | .structDef .. | .typeAlias .. | .refineDef .. | .enumDef .. => pure ()
  | e => e.children.forM nestedReturnsFree

/-- `checkNestedReturns`: in result position. -/
partial def nestedReturnsResult : SExpr → Except String Unit
  | .ret _ (some e) => nestedReturnsResult e
  | .ret _ none => pure ()
  | .block _ es => do
    es.dropLast.forM nestedReturnsFree
    es.getLast?.forM nestedReturnsResult
  | .ite _ cs t (some e) => do cs.forM nestedReturnsFree; nestedReturnsResult t; nestedReturnsResult e
  | .ite _ cs t none => do cs.forM nestedReturnsFree; nestedReturnsFree t
  | .caseE _ sc arms => do
    nestedReturnsFree sc
    arms.forM fun (pt, v) => do pt.forM nestedReturnsFree; nestedReturnsResult v
  | .loop _ b => nestedReturnsFree b
  | .decl _ _ _ _ x => nestedReturnsResult x
  | .structDef .. | .typeAlias .. | .refineDef .. | .enumDef .. => pure ()
  | e => e.children.forM nestedReturnsPart

/-- `checkNestedReturns`: a part of a value returned. -/
partial def nestedReturnsPart : SExpr → Except String Unit
  | .ret p _ => throw s!"{p.show}: a return inside the value a function returns: a return is that value, or a branch of it, or in code whose value is not returned (Book of Verse tests, Return.versetest: \"Return can't be a subexpression of an explicit or implicit return\")"
  | .structDef .. | .typeAlias .. | .refineDef .. | .enumDef .. => pure ()
  | e => e.children.forM nestedReturnsPart
end

/-- A `return` in a function whose result is not `void` is the value of a
    function's body, a branch of it or of a `case`, the operand of a
    `return`, or code whose value is not returned: not a part of a value a
    function returns (Book of Verse tests, `Return.versetest` 114-162: "Return
    can't be a subexpression of an explicit or implicit return, with a few
    exceptions", 3534). The value a function returns (its body's, or a
    `return`'s operand) is read in *result* position: a block's last item,
    both branches of an `if` with an `else`, a `case`'s arms and a
    `return`'s operand are in it too; a block's other items, the conditions
    of an `if`, the body of a `loop` (whose value is `false`) and of an `if`
    with no `else` (whose value is `false` too) are code whose value is not
    returned, where a `return` may be, its own operand in result position;
    anything else in result position (an operator's operands, a call's
    arguments, an array's or a tuple's elements, a construction's fields, a
    `for`'s clauses and body, whose values make its value) is part of the
    value, where no `return` may be. -/
partial def checkNestedReturns (tops : List STop) : Except String Unit := do
  let fn : STop → Except String Unit
    | .fn _ _ _ _ _ ret body => if ret == .name "void" then pure () else nestedReturnsResult body
    | _ => pure ()
  for t in tops do
    match t with
    | .fn .. => fn t
    | .classDef _ _ _ _ _ _ _ _ ms => ms.forM fn
    | _ => pure ()
/-- A `return` or a `break` does not leave a failure context (the Book of
    Verse: `FlowControl/Reachability.versetest:12`, "Explicit return out of a
    failure context is not allowed", error 3535;
    `Bugs/SOL-4199-BreakFromIf.versetest`, "`break` is not allowed in an `if`
    condition", nor in a `for` domain, `option`, `logic`, `not` or the left of
    `or`, error 3658; ch. 7, `07_control.md:530`: `break` "must appear in a code
    block, not as part of a complex expression"). A `return` is refused with a
    failure context between it and its function's body: an `if`'s conditions,
    a `for`'s clauses (its body is none: a `for`'s body may return,
    `Return.versetest:152`), the clauses of `first`, `option{…}`,
    `logic{…}`, the operand of `not` and the left of `or`; and in a
    `<decides>` function, whose body is a failure context, anywhere but in
    tail position (`Return.versetest` 157-163, "Explicit return can only
    occur in failure contexts in a tail position"): the body's last
    expression, the last of a block in tail position, both branches of an
    `if` with an `else` in tail position, a `case`'s arms, the right of
    `and` and `or`, a `return`'s value. A `break` is refused with such a
    context between it and its loop (a `for`'s body is none,
    `SOL-4199-BreakFromIf.versetest:38`). -/
partial def checkJumps (tops : List STop) : Except String Unit := do
  let contexts := "an if's conditions, a for's clauses, first, option{…}, logic{…}, not or the left of or"
  -- (`fn`: a failure context since the function's body; `lp`: since the
  -- innermost loop; `tail`: in tail position, where the function is
  -- `<decides>`, `dec`)
  let rec go (dec fn lp tail : Bool) (e : SExpr) : Except String Unit := do
    let sub := go dec fn lp false
    let ctx := go dec true true false
    match e with
    | .ret p v =>
      if fn then
        throw s!"{p.show}: return cannot leave a failure context ({contexts}): what the context did would not be undone (the Book of Verse's tests, Reachability.versetest:12, SOL-4199-BreakFromIf.versetest:87)"
      if dec && !tail then
        throw s!"{p.show}: a return in a <decides> function must be in tail position (the last expression of its body, or a branch of one), as its body is a failure context (the Book of Verse's tests, Return.versetest:157)"
      v.forM (go dec fn lp true)
    | .brk p =>
      if lp then
        throw s!"{p.show}: break cannot leave a failure context ({contexts}) for its loop (the Book of Verse's tests, SOL-4199-BreakFromIf.versetest)"
    | .block _ es =>
      let n := es.length
      for (x, i) in es.zipIdx do go dec fn lp (tail && i + 1 == n) x
    | .ite _ cs t u => do
      cs.forM ctx
      go dec fn lp (tail && u.isSome) t
      u.forM (go dec fn lp tail)
    | .forE _ cs b => do cs.forM ctx; sub b
    | .loop _ b => go dec fn false false b
    | .caseE _ sc arms => do
      sub sc
      for (pt, v) in arms do
        pt.forM sub
        go dec fn lp tail v
    | .notE _ x | .optionLit _ x | .logicLit _ x => ctx x
    | .orE _ a b => do ctx a; go dec fn lp tail b
    | .andE _ a b => do sub a; go dec fn lp tail b
    | .app _ (.ident _ "$first") args _ => args.forM ctx
    | e => e.children.forM sub
  let isDecides (effs : List String) : Bool := effs.contains "decides"
  let rec goTop : STop → Except String Unit
    | .fn _ _ ps _ effs _ body => do
      ps.forM (·.default.forM (go false false false false))
      go (isDecides effs) false false true body
    | .const _ _ _ _ (.structDef _ _ _ fs) => fs.forM fun f => f.default.forM (go false false false false)
    | .const _ _ _ _ e => go false false false false e
    | .classDef _ _ _ _ _ _ _ fs ms => do
      fs.forM fun f => f.default.forM (go false false false false)
      ms.forM goTop
  tops.forM goTop

/-- The concurrency prelude a program needs (#156), with subscribable
    events' (#210, #220): the prelude's names the program defines itself,
    each with the name the prelude's own definition takes, whether the
    program uses concurrency, and the prelude's definitions. It reads the
    program's names resolved (a module's own `event`, a type parameter named
    `task`, are not the prelude's), and the functions the requests add. -/
def concurrencyHelpers (resolved : List STop) (requests : Requests) (eventFifo : Bool) :
    Except String (List (String × String) × Bool × List STop) := do
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
  let helpers := (← if usesConc then concTops privateNames eventFifo else pure []) ++
    (← if usesSub then subTops privateNames else pure []) ++ (← if usesSubVoid then subVoidTops privateNames else pure [])
  return (concurrencyNames, usesConc, helpers)

/-- Source admission, the first phase of `elabProgramCore`: the program as
    parsed (its attributes taken out, `Attributes.apply`), checked, resolved
    and desugared by these passes, in this order, which is the order of their
    refusals:
    1. the effect policy, with where each specifier may go, and the source
       profile (`EffectPolicy`, `SourceProfile`);
    2. the rules of the source as written: no built-in type's name taken
       (`checkTypeNames`), no reserved name (`checkReservedNames`), each name
       defined once in its scope (`checkDefinedOnce`) and none of a scope
       around it (`checkNoShadowing`), `return` only in a function
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
       (`checkForClauses`), and the places of every `for`'s filters
       (`forFilterPositions`), whose code the elaboration checks can fail;
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
       (`checkConstantOrder`), and the calls of initializers marked
       (`InitializerConvergence.markSource`);
    9. the concurrency prelude the program needs (`concurrencyHelpers`), and
       the construction effects the source declares. -/
def admitSource (allTops0r : List STop) (opts : Options) : Except String Admitted := do
  -- 1. effects and specifiers, and the source profile
  EffectPolicy.check allTops0r opts.entry
  EffectPolicy.checkPlaces allTops0r
  SourceProfile.check opts.profile allTops0r opts.entry
  -- 2. the rules of the source as written, on the definitions as parsed
  checkTypeNames allTops0r
  checkReservedNames allTops0r
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
  let helpers := (← if usesRat then ratTops else pure []) ++ (← if usesReplaceAll then replaceAllTops else pure []) ++
    (← if usesBitwise then bitwiseTops else pure [])
  let intrinsicCalls := helpers.filterMap fun | .fn _ n .. => some n | _ => none
  let ignoredArms := allTops0r.flatMap fun
    | .const _ n _ _ (.block _ es) => if n == ignoredArmsMarker then es.map (·.pos) else []
    | _ => []
  let unmarked := allTops0r.filter fun
    | .const _ n _ _ _ => ![ratMarker, replaceAllMarker, ignoredArmsMarker, bitwiseMarker].contains n
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
  let (concurrencyNames, usesConc, prelude) ← concurrencyHelpers resolved opts.requests opts.eventFifo
  let constructionFx := resolved.foldl (fun budgets top => match top with
    | .classDef _ n _ _ specs .. | .const _ n _ _ (.structDef _ _ specs _) =>
      budgets.insert n (EffectPolicy.constructionFx specs)
    | _ => budgets) ({} : Std.HashMap String (List String))
  return { resolved, rawEntry, typeDefaults, helpers := helpers ++ prelude, intrinsicCalls, concurrencyNames, usesConc,
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
  forFilters : List Pos := []

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
  let cellsIn (ps : List SParam) (b : SExpr) : Bool := cells b || ps.any (·.default.any cells)
  let usesCells := lazy && resolved.any fun
    | .fn _ _ ps _ _ _ b => cellsIn ps b
    | .const _ _ _ _ e => cells e
    | .classDef _ _ _ _ _ _ _ fs ms => fs.any (·.default.any cells) ||
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
          !name.startsWith "$subtypeRefinement" && !name.startsWith "$subtypeBox" then
        throw s!"{p.show}: internal: invalid subtype dictionary request"
    | _ => throw "internal: a subtype dictionary request must be a class"
  let resolved := requests.subtypes ++ loopTops ++ resolved
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
  let argsTop : List STop :=
    match args with
    | some as =>
      if defines "Args" then []
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
