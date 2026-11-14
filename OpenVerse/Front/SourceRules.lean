/-
  OpenVerse front end — the rules of the source as written: what
  `admitSource` (`Elab/Source.lean`) checks of a program's definitions as
  parsed, before any name is resolved (its step 2), each with the words of
  the Book or of its tests it follows, in the order `admitSource` runs them,
  which is the order of their refusals; then the places of the filters the
  elaboration checks can fail (`forFilterPositions`), and the constants'
  rules, which `admitSource` checks once modules are resolved and aliases
  written out (its step 8). They read the syntax only, with the names of
  `Modules` (`qualParts`), `Refine.findPart`, and the functions with
  several values (`Choice`, for `forFilterPositions`), so this file compiles
  before any of the elaborator.
-/
import OpenVerse.Front.Modules
import OpenVerse.Front.Refine

namespace OpenVerse.Front
open OpenVerse

/-- A type of the program's own does not take a built-in type's name
    (`typeNames`): a class, an interface, a struct, an enum or a type alias
    the parser knows (`name := []int`), at the top level or in a module. -/
def checkTypeNames (tops : List STop) : Except String Unit := do
  for t in tops do
    match t with
    | .const p n _ _ (.structDef ..) | .const p n _ _ (.enumDef ..) | .const p n _ _ (.typeAlias ..)
    | .classDef p n .. =>
      let n := (qualParts n).getLastD n
      if typeNames.contains n then throw s!"{p.show}: {n} is a built-in type"
    | _ => pure ()

/-- No definition takes a reserved name (`reservedNames`), at any scope;
    an enum's value takes one, or an access specifier's name, only
    qualified with its enum (Book of Verse ch. 9, `09_structs_enums.md:530`:
    "Qualification also allows you to use reserved words and keywords as
    enum values, which would otherwise cause errors"; `enum{ public }`
    refused, `enum{ (A:)public }` valid, `QualifiedIdentifier.versetest`
    313-316). -/
def checkReservedNames (tops : List STop) : Except String Unit := do
  for t in tops do
    for (p, n) in t.definedNames do
      let n := (n.splitOn "::").getLast?.getD n
      -- (an extension method's, `M` of its function `$ext:M`)
      let n := (extensionMethod? n).getD n
      if reservedNames.contains n then throw s!"{p.show}: '{n}' is reserved: no definition can take it"
    if let .const p e _ _ (.enumDef _ vs _) := t then
      if let some v := vs.find? fun v => (reservedNames ++ EffectPolicy.accessNames).contains v then
        let e := (e.splitOn "::").getLast?.getD e
        throw s!"{p.show}: '{v}' is a reserved word: a value of the enum {e} takes it only qualified, ({e}:){v} (Book of Verse ch. 9)"

/-- The names a definition introduces (`STop.definedNames`) but its
    functions' and methods' own: a function of a built-in type's name is
    the program's, which its calls reach (`any(X)`, #139). -/
partial def STop.namesButFunctions : STop → List (Pos × String)
  | t@(.fn _ n ..) => if n.startsWith "(" then t.definedNames else t.definedNames.drop 1
  | t@(.const ..) => t.definedNames
  | .classDef p _ _ tps _ _ _ fs ms =>
    tps.map (fun tp => (tp.pos, tp.name)) ++
      fs.flatMap (fun f => (p, bareName f.name) :: (f.default.map SExpr.definedNames).getD []) ++
      ms.flatMap STop.namesButFunctions

/-- Nor does another definition, at any scope: a constant, a module, a type
    parameter, a parameter, a local or a field. The built-in types are
    definitions every scope sees (Book of Verse ch. 16, "Automatic
    Qualification": `int` is `(/Verse.org/Verse:)int`), and no definition
    takes the name of one around it (ch. 10, "Shadowing and
    Qualification"); a use of one so named would read the type. A function
    or a method may (`STop.namesButFunctions`), and an enum's value may
    when it is written qualified, `(kind:)int`, as with a reserved word
    (`checkReservedNames`; ch. 9, "Explicit Qualification": "Enumerators
    can collide with identifiers in parent scopes"). -/
def checkBuiltinTypeNames (tops : List STop) : Except String Unit := do
  for t in tops do
    for (p, n) in t.namesButFunctions do
      let n := (qualParts n).getLastD n
      if typeNames.contains n then
        throw s!"{p.show}: '{n}' is the name of a built-in type, which every scope sees (Book of Verse ch. 16: int is (/Verse.org/Verse:)int), and Verse does not allow shadowing (ch. 10): no definition can take it"
    if let .const p e _ _ (.enumDef _ vs _) := t then
      if let some v := vs.find? typeNames.contains then
        let e := (e.splitOn "::").getLast?.getD e
        throw s!"{p.show}: '{v}' is the name of a built-in type: a value of the enum {e} takes it only qualified, ({e}:){v} (Book of Verse ch. 9: \"Enumerators can collide with identifiers in parent scopes\")"

/-- Each name is defined once in its scope, the top level or a module: only
    functions of one scope share a name, as its overloads, and a type alias
    a parametric type's, at another number of type parameters, `t() :=
    t(int)` beside `t(u:type) := class…` (a use names the one of its
    arity, `Aliases.expand`; the Book of Verse's tests,
    `ParametricTypes.versetest:754-768`, `Bugs/SOL-7503…`, `SOL-7849…`). A
    class, an interface, a struct, an enum, a constant and a function of one
    name are two definitions of it (two modules of one name, and a module
    and a definition, are `resolveModules`' to refuse). -/
def checkDefinedOnce (tops : List STop) : Except String Unit := do
  -- (each qualified name seen: whether only functions have it so far, and
  -- each type or type alias of it, its number of type parameters and
  -- whether it is an alias, when it has no other definition)
  let mut seen : Std.HashMap String (Bool × List (Nat × Bool)) := {}
  for t in tops do
    let (p, n, isFn) := match t with
      | .fn p n .. => (p, n, true)
      | .const p n .. | .classDef p n .. => (p, n, false)
    let arity? : Option (Nat × Bool) := match t with
      | .classDef _ _ _ tps .. | .const _ _ _ none (.structDef _ tps ..) => some (tps.length, false)
      | .const _ _ _ none (.typeAlias _ tps _) => some (tps.length, true)
      | _ => none
    -- (not the parser's markers, `$module:…`, nor the compiler's names)
    if (qualParts n).any (·.startsWith "$") then continue
    if let some (onlyFns, types) := seen[n]? then
      -- (one type and one alias of it, at two numbers of type parameters)
      let atArity := match arity?, types with
        | some (k, alias), [(k', alias')] => k != k' && alias != alias'
        | _, _ => false
      if !(isFn && onlyFns) && !atArity then
        -- (two types at two numbers of type parameters: the rule takes only
        -- an alias beside a type)
        let alias := match arity?, types with
          | some (k, _), [(k', _)] => if k != k' then ", and a type alias beside a type of its name at another number of type parameters" else ""
          | _, _ => ""
        throw s!"{p.show}: '{".".intercalate (qualParts n)}' is defined twice (only functions can be overloaded{alias})"
    seen := seen.insert n (isFn && ((seen[n]?).map (·.1)).getD true,
      match arity?, seen[n]? with
      | some a, none => [a]
      | some a, some (_, types) => types ++ [a]
      | none, _ => [])

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

/-- The places of the filters of every `for`, and of every `first` with a
    generator, as written: each clause that is neither a generator (`X : A`,
    `X := A..B`; a `first`'s are the parser's `$each` bindings) nor a
    definition (`X := e`, `X:t = e`, `var X:t = e`), and has no choice in it
    and calls no function with several values, which make it a generator
    over their values (#208, #283). The elaboration checks that each can
    fail (`elabSeqIn`; Book of Verse ch. 7: "Each filter must be failable";
    its tests, `first.versetest:28`: "Only allow expressions that can fail
    (same as `for`)"); a clause that inlining or a choice's preparation
    adds, as the statements of a function with several values that a `for`
    takes, is none of them. -/
partial def forFilterPositions (tops : List STop) : List (Pos × String) :=
  let mv := Choice.multiValued (Choice.multiCandidates tops)
  let callsMulti (c : SExpr) : Bool :=
    Choice.anyE (fun | .app _ (.ident _ f) _ _ => mv.contains f | _ => false) c
  let filters (cs : List SExpr) : List (Pos × String) := cs.filterMap fun c => match c with
    | .gen .. | .decl .. => none
    | c => if Choice.hasChoice [c] || callsMulti c then none else some (c.pos, SExpr.filterKind c)
  let isEach : SExpr → Bool
    | .decl _ _ _ false (.app _ (.ident _ "$each") _ false) => true
    | _ => false
  let rec go : SExpr → List (Pos × String)
    | .forE _ cs b => filters cs ++ cs.flatMap go ++ go b
    | e@(.app _ (.ident _ "$first") [.block _ items] false) =>
      (if items.dropLast.any isEach then filters items.dropLast else []) ++ e.children.flatMap go
    | e => e.children.flatMap go
  tops.flatMap fun t => t.code.flatMap go

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

end OpenVerse.Front
