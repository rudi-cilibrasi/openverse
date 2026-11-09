/-
  OpenVerse front end — choice `a₁ | a₂ | …` (#208), its surface side.

  A choice is parsed as `$choice(a₁, a₂, …)`, an `.app` of a reserved name
  (as `$branch` and `$defer` are), with the alternatives that are choices
  themselves spliced in: `(1 | 2) | 3` is `1 | 2 | 3`.

  A choice has several values (the Verse Calculus's), taken by the nearest
  failure context: all of them by the clauses of a `for`, the first success
  by an `if` condition and by `first{…}`. For now a choice can be the value
  of a binding there (`X := a | b`, `X:t = a | b`), or a clause of its own;
  `normClauses` makes each of those a binding, which the elaborator compiles
  with `Expr.altE`, `Expr.chooseFirst` and `Expr.firstE` (Core/Derived.lean,
  where their behaviour is proved).
-/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front.Choice

/-- The alternatives of a choice. -/
def alts? : SExpr → Option (List SExpr)
  | .app _ (.ident _ "$choice") as false => some as
  | _ => none

def isChoice (e : SExpr) : Bool := (alts? e).isSome

/-- `a₁ | a₂ | …`, with the alternatives that are choices spliced in. -/
def mk (p : Pos) (as : List SExpr) : SExpr :=
  .app p (.ident p "$choice") (as.flatMap fun a => (alts? a).getD [a]) false

/-- A binding of a choice, the form the elaborator compiles. -/
structure Binding where
  pos : Pos
  name : String
  /-- The written type. -/
  ty : Option STy
  alts : List SExpr
  /-- For `set L = a | b`: `L`, at whose type the alternatives are taken. -/
  place : Option SExpr := none
  /-- For an `if` with choices in its branches (#235): the `if`, whose
      branches' alternatives the elaborator guards by the branch taken. -/
  branchy : Option SExpr := none
  /-- For a call of a recursive function with several values (#235): the
      array of its values, `F$all(args)`; the binding takes each in turn. -/
  each : Option SExpr := none

def binding? : SExpr → Option Binding
  | .decl p x ty false (.app _ (.ident _ "$choice") as false) => some ⟨p, x, ty, as, none, none, none⟩
  | .decl p x ty false (.app _ (.ident _ "$choiceAt") (l :: as) false) => some ⟨p, x, ty, as, some l, none, none⟩
  | .decl p x ty false (.app _ (.ident _ "$branchChoice") [i] false) => some ⟨p, x, ty, [], none, some i, none⟩
  | .decl p x ty false (.app _ (.ident _ "$branchChoiceAt") [l, i] false) => some ⟨p, x, ty, [], some l, some i, none⟩
  | .decl p x ty false (.app _ (.ident _ "$each") [a] false) => some ⟨p, x, ty, [], none, none, some a⟩
  | _ => none

/-- An `if … else …` with a choice in a branch (the branches of an `else if`
    chain included): it has the values of the branch its conditions pick. -/
partial def isBranchy : SExpr → Bool
  | i@(.ite _ _ t (some e)) => complete i && (isChoice t || isChoice e || isBranchy t || isBranchy e)
  | _ => false
where
  /-- Every `else if` of the chain has an `else`. -/
  complete : SExpr → Bool
    | .ite _ _ _ (some e@(.ite ..)) => complete e
    | .ite _ _ _ (some _) => true
    | _ => false

/-- The branches of an `if … else if … else …` chain: each one's conditions
    (none for the last `else`) and its expression. -/
partial def arms : SExpr → List (Option (List SExpr) × SExpr)
  | .ite _ cs t (some e) => (some cs, t) :: arms e
  | e => [(none, e)]

/-- The part of a made name that names an inlined call's site (#235), set
    apart from the position after it (site 1 at line 12 is not site 11 at
    line 2); nothing outside one. -/
def sitePart (site : String) : String := if site.isEmpty then "" else site ++ "@"

/-- The indices of a `set` path bound to names, in order (unless literals),
    and the path with those names in their places: `set` evaluates them
    before the new value. -/
partial def hoistPath (q : Pos) (l : SExpr) (site : String := "") : List SExpr × SExpr :=
  let nm (n : Nat) : String := s!"$i{sitePart site}{q.line}_{q.col}_{n}"
  let rec go (n : Nat) : SExpr → List SExpr × SExpr × Nat
    | .app r base args true =>
      let (h, base', n) := go n base
      let (h2, args', n) := args.foldl (fun (h, acc, n) a => match a with
        | .int .. | .char .. | .char32 .. => (h, acc ++ [a], n)
        | a => (h ++ [.decl r (nm n) none false a], acc ++ [.ident r (nm n)], n + 1)) (h, [], n)
      (h2, .app r base' args' true, n)
    | .member r base f =>
      let (h, base', n) := go n base
      (h, .member r base' f, n)
    | .query r base =>
      let (h, base', n) := go n base
      (h, .query r base', n)
    | e => ([], e, n)
  let (h, l', _) := go 0 l
  (h, l')

/-- `set L op= R` whose `R` needs code before it (a choice, or lifted
    operands): `L`'s indices, then for `op=` its old value, then that code,
    as `set` evaluates. `$withOld(O, R)` tells the elaborator that the old
    value is already in `O`. The result: the clauses before, the old value's
    name, and the path. -/
def setPrefix (q : Pos) (l : SExpr) (op : Option String) (site : String := "") :
    List SExpr × Option String × SExpr :=
  let (h, l') := hoistPath q l site
  match op with
  | none => (h, none, l')
  | some _ =>
    let o := s!"$o{sitePart site}{q.line}_{q.col}"
    (h ++ [.decl q o none false l'], some o, l')

/-- The new value of a `set` whose old one is in `o?`. -/
def withOld (q : Pos) (o? : Option String) (r : SExpr) : SExpr :=
  match o? with
  | some o => .app q (.ident q "$withOld") [.ident q o, r] false
  | none => r

/-- `set L op= a | b` with the choice bound first, as `set` evaluates (Book
    of Verse §3.5): the indices of `L`'s path, then for `op=` the old value,
    then the choice. For `=`, the alternatives take `L`'s type. -/
def setClauses (p : Pos) (l : SExpr) (op : Option String) (as : List SExpr) (q : Pos) (site : String := "") :
    List SExpr × SExpr :=
  let (h, o?, l') := setPrefix q l op site
  let c := s!"$c{sitePart site}{q.line}_{q.col}"
  let choice : SExpr := match op with
    | none => .app q (.ident q "$choiceAt") (l' :: as) false
    | some _ => .app q (.ident q "$choice") as false
  (h ++ [.decl q c none false choice], .set p l' op (withOld q o? (.ident q c)))

/-- The clauses, with each choice the value of a binding: a clause that is a
    choice gets a name of its own, and `set L = a | b` and `var X:t = a | b`
    bind the choice first. -/
def normClauses (cs : List SExpr) (site : String := "") : List SExpr :=
  cs.flatMap fun c =>
    let nm (p : Pos) : String := s!"$c{sitePart site}{p.line}_{p.col}"
    match c with
    | .app p (.ident _ "$choice") _ false => [.decl p (nm p) none false c]
    | .set p l op rhs => match alts? rhs with
      | some as => let (h, s) := setClauses p l op as p site; h ++ [s]
      | none => [c]
    | .decl p x ty true rhs =>
      if isChoice rhs then [.decl p (nm p) ty false rhs, .decl p x ty true (.ident p (nm p))] else [c]
    -- (`set L = a | b` as the last clause of a macro, which names its value)
    | .decl p x ty false (.set q l op rhs) => match alts? rhs with
      | some as => let (h, s) := setClauses q l op as q site; h ++ [.decl p x ty false s]
      | none => [c]
    | c => [c]

/-! ### A choice inside an expression

A choice in an operand is lifted out of its clause (A-normal form): the
operands evaluated before it are bound to fresh names first, so that they
still run once and before it, then the choice itself, and the clause keeps
the choice's name in its place:

    X := F() + (1 | 2)    ⟶    $t := F(), $c := 1 | 2, X := $t + $c

Lifting goes through the operands that are evaluated left to right, once
each: those of arithmetic, comparisons, calls (the receiver first), member
access, `?`, tuples, arrays, maps and string interpolation. A choice
elsewhere (in a block, a branch, a struct construction, whose fields are
evaluated in declaration order, a named argument, or an alternative) is not
lifted, and the elaborator refuses it. -/

/-- The variable a `set` path starts from. -/
partial def rootName? : SExpr → Option String
  | .ident _ n => some n
  | .member _ e _ | .app _ e _ true => rootName? e
  | _ => none

/-- The names that `set` writes inside `e`. -/
partial def setsIn : SExpr → List String
  | .set _ l _ r => ((rootName? l).map ([·])).getD [] ++ setsIn l ++ setsIn r
  | .app _ f as _ => setsIn f ++ as.flatMap setsIn
  | .member _ e _ | .query _ e | .neg _ e | .notE _ e | .optionLit _ e | .logicLit _ e | .loop _ e => setsIn e
  | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b => setsIn a ++ setsIn b
  | .cmp _ a rest => setsIn a ++ rest.flatMap (setsIn ·.2)
  | .tuple _ es | .block _ es | .arrayLit _ es => es.flatMap setsIn
  | .ite _ cs t e => cs.flatMap setsIn ++ setsIn t ++ ((e.map setsIn).getD [])
  | .forE _ cs b => cs.flatMap setsIn ++ setsIn b
  | .gen _ _ _ s => setsIn s
  | .ret _ e => (e.map setsIn).getD []
  | .caseE _ s arms => setsIn s ++ arms.flatMap fun (p, v) => ((p.map setsIn).getD []) ++ setsIn v
  | .decl _ _ _ _ e => setsIn e
  | .construct _ _ _ fs => fs.flatMap setsIn
  | .mapLit _ kvs => kvs.flatMap fun (k, v) => setsIn k ++ setsIn v
  | .str _ ps => ps.flatMap fun | .code c => setsIn c | .text _ => []
  | _ => []

/-- The names a clause list binds (so values, for `stable` and the heads
    of calls). -/
def boundIn (cs : List SExpr) : List String :=
  cs.flatMap fun
    | .decl _ x _ _ _ => [x]
    | .gen _ x i _ => x :: i.toList
    | _ => []

/-- The receiver of a method or field. -/
def recvOf : SExpr → SExpr
  | .member _ obj _ => obj
  | e => e

/-- What a call's head evaluates before its arguments, as operands: a head
    that is a value (a variable holding an array, a map or a function, `isVal`
    says which names are), the receiver of a method or field (unless a
    module, class or other name that is no value), or any other expression;
    not a function's or class's name. -/
def headOps (isVal : String → Bool) (isField : String → String → Bool) : SExpr → List SExpr × Bool
  | f@(.ident _ n) => if isVal n then ([f], true) else ([], true)
  -- (a field holding an array, map or function is read whole, first; a
  -- method's receiver only)
  | f@(.member _ (.ident _ n) m) =>
    if isField n m then ([f], true) else if isVal n then ([recvOf f], false) else ([], false)
  | f@(.member _ _ _) => ([recvOf f], false)
  | f => ([f], true)


/-- Whether a call's head has a choice that lifting reaches. -/
partial def headHas (hasL : SExpr → Bool) : SExpr → Bool
  | .ident .. => false
  | .member _ obj _ => hasL obj
  | f => hasL f

/-- Whether `e` has a choice that lifting reaches. -/
partial def hasLiftable : SExpr → Bool
  | .app _ (.ident _ "$choice") _ false => true
  | .app _ (.ident _ "$inline") _ false => true
  | .app _ (.ident _ "$each") _ false => true
  | e@(.ite ..) => isBranchy e
  | .app _ f args _ => headHas hasLiftable f || args.any fun a =>
      (match a with | .decl _ n _ _ _ => !n.startsWith "?" | _ => true) && hasLiftable a
  | .bin _ _ a b => hasLiftable a || hasLiftable b
  | .cmp _ a rest => hasLiftable a || rest.any (hasLiftable ·.2)
  | .member _ e _ | .query _ e | .neg _ e => hasLiftable e
  | .tuple _ es | .arrayLit _ es => es.any hasLiftable
  | .str _ ps => ps.any fun | .code c => hasLiftable c | .text _ => false
  | .mapLit _ kvs => kvs.any fun (k, v) => hasLiftable k || hasLiftable v
  | _ => false

/-- The same whenever evaluated, and typed by where they are (so they keep
    their expected type in place), so not bound to a name of their own:
    literals, `array{}`, `map{}`, and names that are no values (functions,
    classes, enumerators, `true`, `false`). Not names of values: a bare name
    may be a variable an alternative sets, or a field of `Self` that its
    method call changes. -/
partial def stable (isVal : String → Bool) : SExpr → Bool
  | .int .. | .char .. | .char32 .. | .float .. => true
  | .neg _ e => stable isVal e
  | .str _ ps => ps.all fun | .text _ => true | .code _ => false
  | .arrayLit _ es | .tuple _ es => es.all (stable isVal)
  | .mapLit _ kvs => kvs.all fun (k, v) => stable isVal k && stable isVal v
  | .optionLit _ (.block _ [e]) => stable isVal e
  | .ident _ n => !isVal n
  | .member _ (.ident _ n) _ => !isVal n
  | _ => false

structure LiftSt where
  next : Nat := 0
  /-- The clauses lifted so far, in order. -/
  pre : Array SExpr := #[]
  /-- Part of every name made: the call site of the function being inlined
      (#235), so two calls of one function do not make the same names. -/
  site : String := ""

abbrev LM := StateM LiftSt

def LM.fresh (p : Pos) (k : String) : LM String :=
  modifyGet fun s => (s!"${k}{sitePart s.site}{p.line}_{p.col}_{s.next}", { s with next := s.next + 1 })

def LM.bind (p : Pos) (k : String) (e : SExpr) : LM SExpr := do
  let x ← LM.fresh p k
  modify fun s => { s with pre := s.pre.push (.decl p x none false e) }
  return .ident p x

mutual
/-- `e` with its liftable choices lifted (into the state's clauses). -/
partial def liftE (isVal : String → Bool) (isField : String → String → Bool) (e : SExpr) : LM SExpr := do
  if !hasLiftable e then return e
  match e with
  | .app p (.ident _ "$choice") _ false => LM.bind p "c" e
  | .ite p .. => LM.bind p "c" (.app p (.ident p "$branchChoice") [e] false)
  | .app p (.ident q "$each") [.app p2 g args br] false =>
    -- (a call of a recursive function with several values, #235: the
    -- choices in its arguments lifted, then each argument bound, so that
    -- one that fails is a clause that fails where it is, before the array
    -- of the function's values is computed)
    let args' ← liftOps isVal isField args
    let args'' ← args'.mapM fun a => if stable isVal a then pure a else LM.bind a.pos "t" a
    LM.bind p "c" (.app p (.ident q "$each") [.app p2 g args'' br] false)
  | .app p (.ident _ "$each") _ false => LM.bind p "c" e
  | .app _ (.ident _ "$inline") (_ :: .block _ tmpl :: args) false =>
    -- a call of a function with several values (#235): the arguments, in
    -- order, into its (renamed) parameters, then its body's clauses, then
    -- its value's name
    let (pds, body) := (tmpl.take args.length, tmpl.drop args.length)
    -- (the callee's declared effects, which the caller must allow, as at a
    -- call: noted by `$fxOf`, since no call is left)
    if let .app _ _ (fn :: _) _ := e then
      modify fun s => { s with pre := s.pre.push (.app fn.pos (.ident fn.pos "$fxOf") [fn] false) }
    for (pd, a) in pds.zip args do
      let a' ← liftE isVal isField a
      match pd with
      | .decl q x ty v _ => modify fun s => { s with pre := s.pre.push (.decl q x ty v a') }
      | _ => pure ()
    match body.getLast? with
    | some (.decl q r _ _ _) =>
      let saved := (← get).site
      modify fun s => { s with site := r }
      -- (the body's own names are values too: its parameters and locals)
      let bound := boundIn tmpl
      let isVal' := fun n => isVal n || bound.contains n
      for c in body do
        for c' in normClauses (← liftClauseM isVal' isField c) r do
          modify fun s => { s with pre := s.pre.push c' }
      modify fun s => { s with site := saved }
      return .ident q r
    -- (no template: only seeing whether a body has several values)
    | _ => LM.bind e.pos "c" e
  | .app p f args br =>
    let (hs, whole) := headOps isVal isField f
    let ops := hs ++ args
    -- (named arguments are evaluated after the positional ones: one before
    -- the last choice would change places, so then no lifting)
    let last := (ops.zipIdx.filter (hasLiftable ·.1)).getLast?.map (·.2)
    let named := ops.zipIdx.any fun (a, i) => (match a with
      | .decl _ n _ _ _ => n.startsWith "?" | _ => false) && last.any (i < ·)
    if named then return e
    let ops' ← liftOps isVal isField ops
    let hs' := ops'.take hs.length
    let args' := ops'.drop hs.length
    let f' := match f, hs' with
      | .member q _ m, [o] => if whole then o else .member q o m
      | _, [h] => h
      | _, _ => f
    return .app p f' args' br
  | .bin p o a b => match ← liftOps isVal isField [a, b] with
    | [a', b'] => return .bin p o a' b'
    | _ => return e
  | .cmp p a rest => liftCmp isVal isField p (a :: rest.map (·.2)) (rest.map (·.1))
  | .member p x m => return .member p (← liftE isVal isField x) m
  | .query p x => return .query p (← liftE isVal isField x)
  | .neg p x => return .neg p (← liftE isVal isField x)
  | .tuple p es => return .tuple p (← liftOps isVal isField es)
  | .arrayLit p es => return .arrayLit p (← liftOps isVal isField es)
  | .str p ps =>
    let codes := ps.filterMap fun | .code c => some c | .text _ => none
    let codes' ← liftOps isVal isField codes
    let rec put : List SPart → List SExpr → List SPart
      | .code _ :: ps, c :: cs => .code c :: put ps cs
      | p :: ps, cs => p :: put ps cs
      | [], _ => []
    return .str p (put ps codes')
  | .mapLit p kvs =>
    let flat ← liftOps isVal isField (kvs.flatMap fun (k, v) => [k, v])
    let rec pairs : List SExpr → List (SExpr × SExpr)
      | k :: v :: r => (k, v) :: pairs r
      | _ => []
    return .mapLit p (pairs flat)
  | e => return e

/-- A comparison chain `o₀ op₁ o₁ op₂ …` whose operand `oⱼ` is the first with
    a choice: `o₀ … oⱼ₋₁` are bound to names, the pairs among them checked
    (the chain stops at the first that fails, before the choice), then the
    rest of the chain goes on from `oⱼ₋₁`. Its value is `o₀`. -/
partial def liftCmp (isVal : String → Bool) (isField : String → String → Bool) (p : Pos)
    (os : List SExpr) (syms : List String) : LM SExpr := do
  match (os.zipIdx.find? (hasLiftable ·.1)).map (·.2) with
  | none =>
    match os with
    | o :: more => return .cmp p o (syms.zip more)
    | [] => return .tuple p []
  | some 0 =>
    -- (the choice in the first operand: lifted, then the chain from it)
    match os with
    | o :: more => liftCmp isVal isField p ((← liftE isVal isField o) :: more) syms
    | [] => return .tuple p []
  | some j =>
    -- (the operands before it, each bound, then the pairs among them)
    let mut hs : Array SExpr := #[]
    for o in os.take j do
      hs := hs.push (← if stable isVal o then pure o else LM.bind o.pos "t" o)
    let h0 := hs[0]!
    if j ≥ 2 then
      modify fun s => { s with pre := s.pre.push (.cmp p h0 ((syms.take (j - 1)).zip (hs.toList.drop 1))) }
    let oj ← liftE isVal isField os[j]!
    let r ← liftCmp isVal isField p (hs.back! :: oj :: os.drop (j + 1)) (syms.drop (j - 1))
    if j == 1 then return r
    -- (the rest checked as a clause; the chain's value is its first operand)
    modify fun s => { s with pre := s.pre.push r }
    return h0

/-- Operands evaluated left to right: the liftable choices of each are
    lifted, and every operand before the last one with such a choice is
    bound to a name first (unless `stable`), so it still runs before it. -/
partial def liftOps (isVal : String → Bool) (isField : String → String → Bool) (es : List SExpr) :
    LM (List SExpr) := do
  let last := (es.zipIdx.filter (hasLiftable ·.1)).getLast?.map (·.2)
  match last with
  | none => return es
  | some j =>
    let mut out := #[]
    for (e, i) in es.zipIdx do
      if i < j then
        let e' ← liftE isVal isField e
        out := out.push (← if stable isVal e' then pure e' else LM.bind e.pos "t" e')
      else if i == j then out := out.push (← liftE isVal isField e)
      else out := out.push e
    return out.toList

/-- `liftClause` in the current state (an inlined body's clauses, #235). -/
partial def liftClauseM (isVal : String → Bool) (isField : String → String → Bool) (c : SExpr) :
    LM (List SExpr) := do
  let run (k : LM SExpr) : LM (List SExpr) := do
    let saved := (← get).pre
    modify fun s => { s with pre := #[] }
    let c' ← k
    let pre := (← get).pre
    modify fun s => { s with pre := saved }
    return pre.toList ++ [c']
  let site := (← get).site
  match c with
  | .app _ (.ident _ "$choice") _ false => return [c]
  -- (an `if` with choices in its branches as a binding's value: at its
  -- written type, #235)
  | .decl p x ty false rhs@(.ite ..) =>
    if isBranchy rhs then return [.decl p x ty false (.app p (.ident p "$branchChoice") [rhs] false)] else
      if !hasLiftable rhs then return [c] else run do return .decl p x ty false (← liftE isVal isField rhs)
  | .decl p x ty true rhs@(.ite ..) =>
    if isBranchy rhs then
      let n := s!"$c{sitePart site}{p.line}_{p.col}"
      return [.decl p n ty false (.app p (.ident p "$branchChoice") [rhs] false), .decl p x ty true (.ident p n)]
    else if !hasLiftable rhs then return [c] else run do return .decl p x ty true (← liftE isVal isField rhs)
  | .set p l none rhs@(.ite ..) =>
    if isBranchy rhs then
      let (h, _, l') := setPrefix p l none site
      let n := s!"$c{sitePart site}{p.line}_{p.col}"
      return h ++ [.decl p n none false (.app p (.ident p "$branchChoiceAt") [l', rhs] false), .set p l' none (.ident p n)]
    else if !hasLiftable rhs then return [c] else
      let (h, o?, l') := setPrefix p l none site
      return h ++ (← run do return .set p l' none (withOld p o? (← liftE isVal isField rhs)))
  -- (`set L = …` as the last clause of a macro, which names its value)
  | .decl p x ty v (.set q l op r) =>
    if isChoice r || !hasLiftable r then return [c] else
      let (h, o?, l') := setPrefix q l op site
      return h ++ (← run do return .decl p x ty v (.set q l' op (withOld q o? (← liftE isVal isField r))))
  | .decl p x ty v rhs =>
    if isChoice rhs || !hasLiftable rhs then return [c] else run do
      return .decl p x ty v (← liftE isVal isField rhs)
  | .set p l op rhs =>
    if isChoice rhs || !hasLiftable rhs then return [c] else
      -- (the path's indices, then for `op=` the old value, then the
      -- lifted code, as `set` evaluates)
      let (h, o?, l') := setPrefix p l op site
      return h ++ (← run do return .set p l' op (withOld p o? (← liftE isVal isField rhs)))
  | .gen p x i src =>
    if !hasLiftable src then return [c] else run do return .gen p x i (← liftE isVal isField src)
  | e => if !hasLiftable e then return [c] else run (liftE isVal isField e)
end

/-- A clause with the liftable choices inside it lifted: the clauses before
    it, then it. A binding or `set` whose value is a choice, or a clause that
    is one, stays as it is (`normClauses` makes it a binding). -/
def liftClause (isVal : String → Bool) (isField : String → String → Bool) (c : SExpr)
    (site : String := "") : List SExpr :=
  (liftClauseM isVal isField c).run' { site }

/-- The clauses ready for compiling: choices inside expressions lifted, and
    each choice the value of a binding. `isVal` says which names are values
    (variables and fields in scope); the clauses' own bindings are too. -/
def prepare (cs : List SExpr) (isVal : String → Bool := fun _ => false)
    (isField : String → String → Bool := fun _ _ => false) (site : String := "") : List SExpr :=
  let bound := boundIn cs
  normClauses (cs.flatMap (liftClause (fun n => isVal n || bound.contains n) isField · site)) site

/-- Whether the clauses have a choice for their failure context to take. -/
def hasChoice (cs : List SExpr) : Bool := (prepare cs).any fun c => (binding? c).isSome

/-- `first{cs}`, the last clause naming its value. -/
def firstOfClauses (p : Pos) (cs : List SExpr) : SExpr :=
  let (cs', v) : List SExpr × SExpr := match cs.getLast? with
    | some (.decl q x _ _ _) => (cs, .ident q x)
    | some e =>
      let q := e.pos
      let x := s!"$f{q.line}_{q.col}"
      (cs.dropLast ++ [.decl q x none false e], .ident q x)
    | none => (cs, .tuple p [])
  .app p (.ident p "$first") [.block p (cs' ++ [v])] false

/-- With a choice to take, `e` as the first success of it (#208): how
    `option{…}` and `logic{…}` (whose braces hold clauses), `not` and the left
    of `or` take a choice's values. -/
def takeFirst? : SExpr → Option SExpr
  | .block p cs => if hasChoice cs then some (firstOfClauses p cs) else none
  | e => if hasLiftable e then some (firstOfClauses e.pos [e]) else none

/-! ### Functions with several values (#235)

A top-level function whose body has a choice that no failure context in
it takes (`Digit():int = 0 | 1 | … | 9`) has several values. A call of one
is a choice point: `inlineMulti` drops the function and turns each call into
`$inline(F, template, args…)`, whose template is the body with its
parameters and locals renamed for that call; lifting (`liftE`) puts the
arguments into the parameters, then the body's clauses, into the caller's
clauses, so the body's choices become the caller's. Recursive and generic
ones, ones with named parameters or `return`, and their use as values are
refused for now. -/

/-- `e` with `f` applied top-down: where `f` gives a replacement, it is used
    (and not descended into). Struct constructions' field names are kept. -/
partial def mapE (f : SExpr → Option SExpr) (e : SExpr) : SExpr :=
  match f e with
  | some e' => e'
  | none =>
    let go := mapE f
    match e with
    | .str p ps => .str p (ps.map fun | .code c => .code (go c) | t => t)
    | .app p g as b => .app p (go g) (as.map go) b
    | .member p x m => .member p (go x) m
    | .query p x => .query p (go x)
    | .neg p x => .neg p (go x)
    | .notE p x => .notE p (go x)
    | .bin p o a b => .bin p o (go a) (go b)
    | .cmp p a r => .cmp p (go a) (r.map fun (o, b) => (o, go b))
    | .andE p a b => .andE p (go a) (go b)
    | .orE p a b => .orE p (go a) (go b)
    | .range p a b => .range p (go a) (go b)
    | .tuple p es => .tuple p (es.map go)
    | .block p es => .block p (es.map go)
    | .arrayLit p es => .arrayLit p (es.map go)
    | .optionLit p x => .optionLit p (go x)
    | .logicLit p x => .logicLit p (go x)
    | .ite p cs t e' => .ite p (cs.map go) (go t) (e'.map go)
    | .forE p cs b => .forE p (cs.map go) (go b)
    | .gen p x i src => .gen p x i (go src)
    | .loop p b => .loop p (go b)
    | .ret p x => .ret p (x.map go)
    | .caseE p sc arms => .caseE p (go sc) (arms.map fun (pt, v) => (pt.map go, go v))
    | .decl p n t v x => .decl p n t v (go x)
    | .set p l o r => .set p (go l) o (go r)
    | .construct p n ts fs => .construct p n ts (fs.map fun
        | .decl q fn t v x => .decl q fn t v (go x)
        | a => go a)
    | .mapLit p kvs => .mapLit p (kvs.map fun (k, v) => (go k, go v))
    | .structDef p tps fs => .structDef p tps (fs.map fun (n, t, d, v) => (n, t, d.map go, v))
    | e => e

/-- Whether some subexpression satisfies `pr` (through `mapE`). -/
partial def anyE (pr : SExpr → Bool) (e : SExpr) : Bool :=
  pr e || match e with
    | .str _ ps => ps.any fun | .code c => anyE pr c | _ => false
    | .app _ g as _ => anyE pr g || as.any (anyE pr)
    | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x
    | .gen _ _ _ x | .decl _ _ _ _ x => anyE pr x
    | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => anyE pr a || anyE pr b
    | .cmp _ a r => anyE pr a || r.any (anyE pr ·.2)
    | .tuple _ es | .block _ es | .arrayLit _ es | .construct _ _ _ es => es.any (anyE pr)
    | .ite _ cs t e' => cs.any (anyE pr) || anyE pr t || (e'.map (anyE pr)).getD false
    | .forE _ cs b => cs.any (anyE pr) || anyE pr b
    | .ret _ x => (x.map (anyE pr)).getD false
    | .caseE _ sc arms => anyE pr sc || arms.any fun (pt, v) => ((pt.map (anyE pr)).getD false) || anyE pr v
    | .mapLit _ kvs => kvs.any fun (k, v) => anyE pr k || anyE pr v
    | _ => false

/-- The statements of a body. -/
def stmtsOf : SExpr → List SExpr
  | .block _ ss => ss
  | e => [e]

/-- Calls of the functions `mv` as `$inline` markers with an empty template:
    enough to see whether a body has several values. -/
def markCalls (mv : List String) : SExpr → SExpr :=
  mapE fun
    | .app p (.ident q g) as _ =>
      if mv.contains g then some (.app p (.ident p "$inline") (.ident q g :: .block p [] :: as) false)
      else none
    | _ => none

/-- The names a body binds (its locals), struct fields and named arguments
    aside. -/
partial def localsOf (e : SExpr) : List String :=
  let rec go : SExpr → List String
    | .decl _ n _ _ x => (if n.startsWith "?" then [] else [n]) ++ go x
    | .gen _ x i src => x :: i.toList ++ go src
    | .construct _ _ _ fs => fs.flatMap fun | .decl _ _ _ _ x => go x | a => go a
    | .str _ ps => ps.flatMap fun | .code c => go c | _ => []
    | .app _ g as _ => go g ++ as.flatMap go
    | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x => go x
    | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => go a ++ go b
    | .cmp _ a r => go a ++ r.flatMap (go ·.2)
    | .tuple _ es | .block _ es | .arrayLit _ es => es.flatMap go
    | .ite _ cs t e' => cs.flatMap go ++ go t ++ ((e'.map go).getD [])
    | .forE _ cs b => cs.flatMap go ++ go b
    | .ret _ x => (x.map go).getD []
    | .caseE _ sc arms => go sc ++ arms.flatMap fun (pt, v) => ((pt.map go).getD []) ++ go v
    | .mapLit _ kvs => kvs.flatMap fun (k, v) => go k ++ go v
    | _ => []
  (go e).eraseDups

/-- `e` with the names in `ren` renamed, binders and uses. -/
partial def renameE (ren : List (String × String)) : SExpr → SExpr :=
  mapE fun
    | .ident p n => (ren.lookup n).map (.ident p ·)
    | .decl p n t v x => (ren.lookup n).map fun n' => .decl p n' t v (renameE ren x)
    | .gen p x i src => if (ren.lookup x).isSome || (i.bind fun j => ren.lookup j).isSome then
        some (.gen p ((ren.lookup x).getD x) (i.map fun j => (ren.lookup j).getD j) (renameE ren src)) else none
    | _ => none

/-- A function of the program, by name: its parameters, type parameters,
    effects, result type and body. -/
structure MFn where
  pos : Pos
  params : List SParam
  tparams : List TParam
  fx : List String
  ret : STy
  body : SExpr

/-- The names `e` uses: as identifiers and as calls' heads. -/
partial def namesUsed (e : SExpr) : List String :=
  let rec go : SExpr → List String
    | .ident _ n => [n]
    | .decl _ _ _ _ x => go x
    | .gen _ _ _ src => go src
    | .construct _ _ _ fs => fs.flatMap fun | .decl _ _ _ _ x => go x | a => go a
    | .str _ ps => ps.flatMap fun | .code c => go c | _ => []
    | .app _ g as _ => go g ++ as.flatMap go
    | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x => go x
    | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => go a ++ go b
    | .cmp _ a r => go a ++ r.flatMap (go ·.2)
    | .tuple _ es | .block _ es | .arrayLit _ es => es.flatMap go
    | .ite _ cs t e' => cs.flatMap go ++ go t ++ ((e'.map go).getD [])
    | .forE _ cs b => cs.flatMap go ++ go b
    | .ret _ x => (x.map go).getD []
    | .caseE _ sc arms => go sc ++ arms.flatMap fun (pt, v) => ((pt.map go).getD []) ++ go v
    | .mapLit _ kvs => kvs.flatMap fun (k, v) => go k ++ go v
    | .structDef _ _ fs => fs.flatMap fun (_, _, d, _) => (d.map go).getD []
    | _ => []
  (go e).eraseDups

/-- `e` with every choice `a₁ | … | aₙ` made `if (false?) then a₁ else …
    aₙ`: the body a function with several values keeps, elaborated (so
    type- and effect-checked like any function's) but never called, as its
    calls are inlined. -/
partial def checkBody : SExpr → SExpr :=
  mapE fun
    | .app p (.ident _ "$choice") as false =>
      let rec chain : List SExpr → SExpr
        | [] => .tuple p []
        | [a] => checkBody a
        | a :: rest => .ite p [.query p (.ident p "false")] (checkBody a) (some (chain rest))
      some (chain as)
    | _ => none

/-- Replace each call of a function of `mv` by `$inline(F, template, args…)`,
    each with its own call site (`n`, the sites so far). -/
partial def inlineCalls (mv : List (String × MFn)) (e : SExpr) (recs : List String := []) :
    StateT Nat (Except String) SExpr := do
  let go := fun x => inlineCalls mv x recs
  match e with
  | .app p (.ident q g) as br =>
    match mv.lookup g with
    | some f =>
      -- (as at a call: several arguments to a single array parameter, and
      -- one tuple argument to several parameters, #134, #140)
      let arrayParam := match f.params with | [sp] => (match sp.ty with | .arr _ => true | _ => false) | _ => false
      let tupleArg := as.length == 1 && f.params.length ≥ 2
      if as.length != f.params.length && !arrayParam && !tupleArg then
        throw s!"{p.show}: {g} takes {f.params.length} argument(s), found {as.length}"
      if as.any (fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false) then
        throw s!"{p.show}: {g} has no named parameters"
      if br != f.fx.contains "decides" then
        throw (if br then s!"{p.show}: {g} is not <decides>: call it with {g}(…)"
          else s!"{p.show}: {g} is <decides>: call it with {g}[…]")
      let as' ← as.mapM go
      -- (a recursive one: the array of its values, computed at the call)
      if recs.contains g then
        return .app p (.ident p "$each") [.app p (.ident q s!"{g}$all") as' false] false
      let site ← modifyGet fun n => (n, n + 1)
      if site ≥ 2000 then
        throw s!"{p.show}: more than 2000 calls of functions with several values to inline: nested calls multiply them (#235)"
      let tag (n : String) : String := s!"${g.replace "::" "_"}_{n}_{site}"
      let ren := (f.params.map (·.name) ++ localsOf f.body).eraseDups.map fun n => (n, tag n)
      let body ← go (renameE ren f.body)
      let ss := stmtsOf body
      let r := tag "$r"
      let (init, last) := (ss.dropLast, ss.getLast?)
      let (init, res) : List SExpr × SExpr := match last with
        | some (.decl q2 x t v rhs) => (init ++ [.decl q2 x t v rhs], .ident q2 x)
        | some l => (init, l)
        | none => (init, .tuple q [])
      let (pds, unpack, as'') : List SExpr × List SExpr × List SExpr :=
        if as.length == f.params.length then
          (f.params.map fun sp => SExpr.decl q (tag sp.name) (some sp.ty) false (.ident q "$arg"), [], as')
        else if arrayParam then
          (f.params.map fun sp => SExpr.decl q (tag sp.name) (some sp.ty) false (.ident q "$arg"), [],
            [.arrayLit p as'])
        else
          -- (the tuple bound once, its elements into the parameters)
          let t := tag "$tuple"
          ([.decl q t (some (.tup (f.params.map (·.ty)))) false (.ident q "$arg")],
            (f.params.zipIdx.map fun (sp, i) =>
              SExpr.decl q (tag sp.name) (some sp.ty) false (.app q (.ident q t) [.int q (i : Int)] false)), as')
      let tmpl := SExpr.block q (pds ++ unpack ++ init ++ [.decl q r (some f.ret) false res])
      return .app p (.ident p "$inline") (.ident q g :: tmpl :: as'') false
    | none => return .app p (← go (.ident q g)) (← as.mapM go) br
  | .str p ps => return .str p (← ps.mapM fun | .code c => do return .code (← go c) | t => pure t)
  | .app p g as b => return .app p (← go g) (← as.mapM go) b
  | .member p x m => return .member p (← go x) m
  | .query p x => return .query p (← go x)
  | .neg p x => return .neg p (← go x)
  | .notE p x => return .notE p (← go x)
  | .bin p o a b => return .bin p o (← go a) (← go b)
  | .cmp p a r => return .cmp p (← go a) (← r.mapM fun (o, b) => do return (o, ← go b))
  | .andE p a b => return .andE p (← go a) (← go b)
  | .orE p a b => return .orE p (← go a) (← go b)
  | .range p a b => return .range p (← go a) (← go b)
  | .tuple p es => return .tuple p (← es.mapM go)
  | .block p es => return .block p (← es.mapM go)
  | .arrayLit p es => return .arrayLit p (← es.mapM go)
  | .optionLit p x => return .optionLit p (← go x)
  | .logicLit p x => return .logicLit p (← go x)
  | .ite p cs t e' => return .ite p (← cs.mapM go) (← go t) (← e'.mapM go)
  | .forE p cs b => return .forE p (← cs.mapM go) (← go b)
  | .gen p x i src => return .gen p x i (← go src)
  | .loop p b => return .loop p (← go b)
  | .ret p x => return .ret p (← x.mapM go)
  | .caseE p sc arms => return .caseE p (← go sc) (← arms.mapM fun (pt, v) => do
      return (← pt.mapM go, ← go v))
  | .decl p n t v x => return .decl p n t v (← go x)
  | .set p l o r => return .set p (← go l) o (← go r)
  | .construct p n ts fs => return .construct p n ts (← fs.mapM fun
      | .decl q fn t v x => do return .decl q fn t v (← go x)
      | a => go a)
  | .mapLit p kvs => return .mapLit p (← kvs.mapM fun (k, v) => do return (← go k, ← go v))
  | .structDef p tps fs => return .structDef p tps (← fs.mapM fun (n, t, d, v) => do return (n, t, ← d.mapM go, v))
  | e => return e

mutual
/-- The array of an expression's values, for a `$all` body (#235): a choice
    concatenates its alternatives' arrays, an `if` with choices in its
    branches picks a branch's, and any other expression is the array of the
    values of its own clauses (`gensOf`): of its value, empty when it fails,
    and through the choices and calls of functions with several values
    (marked `$each`) inside it. So an alternative that fails, or whose
    argument does, gives no values, and the others still do. At the written
    type `ty`, when there is one. -/
partial def arrOfE (ty : Option STy := none) : SExpr → SExpr
  | .app p (.ident _ "$choice") as false =>
    match as with
    | [a] => arrOfE ty a
    | _ => .app p (.ident p "Concatenate") (as.map (arrOfE ty)) false
  | .ite p cs t (some e) => .ite p cs (arrOfE ty t) (some (arrOfE ty e))
  | a =>
    let p := a.pos
    let site := s!"a{p.line}_{p.col}"
    let v := s!"$a{p.line}_{p.col}"
    .forE p (gensOf site [.decl p v ty false a]) (.ident p v)

/-- Clauses for a `for` that goes through all their values (#235): each
    choice a generator over the array of its alternatives' values, each
    call of a recursive function with several values one over its array.
    Names made include `site`, so that nested ones differ. -/
partial def gensOf (site : String) (cs : List SExpr) : List SExpr :=
  let nm (q : Pos) : String := s!"$e{sitePart site}{q.line}_{q.col}"
  (prepare cs (site := site)).flatMap fun c => match binding? c with
    | some { pos := q, name := x, ty := ty, alts := as, branchy := none, each := none, .. } =>
      let src := arrOfE ty (.app q (.ident q "$choice") as false)
      match ty with
      | none => [.gen q x none src]
      | some t => [.gen q (nm q) none src, .decl q x (some t) false (.ident q (nm q))]
    | some { pos := q, name := x, ty := ty, branchy := some i, .. } =>
      match ty with
      | none => [.gen q x none (arrOfE none i)]
      | some t => [.gen q (nm q) none (arrOfE (some t) i), .decl q x (some t) false (.ident q (nm q))]
    | some { pos := q, name := x, ty := ty, each := some a, .. } =>
      match ty with
      | none => [.gen q x none a]
      | some t => [.gen q (nm q) none a, .decl q x (some t) false (.ident q (nm q))]
    | _ => [c]
end

/-- Each call of a function of `mvs` marked as the array of its values,
    `$each(F$all(args))`, also in the arguments of others. -/
partial def markAll (mvs : List String) : SExpr → SExpr :=
  mapE fun
    | .app p (.ident q g) as _ =>
      if mvs.contains g then
        some (.app p (.ident p "$each") [.app p (.ident q s!"{g}$all") (as.map (markAll mvs)) false] false)
      else none
    | _ => none

/-- The body of `F$all`, the array of `F`'s values in order (#235): one
    `for` over its clauses (`gensOf`), whose value is `F`'s, at its result
    type `ret`. (`F` is effect-free, so evaluating the clauses in this order
    changes nothing.) -/
def allBody (mvs : List String) (ret : STy) (b : SExpr) : SExpr :=
  let ss := stmtsOf (markAll mvs b)
  let p := b.pos
  let (cs, v) : List SExpr × SExpr := match ss.getLast? with
    | some (.decl q x _ _ _) => (ss, .ident q x)
    | some l => (ss.dropLast ++ [.decl l.pos "$val" (some ret) false l], .ident l.pos "$val")
    | none => ([], .tuple p [])
  .forE p (gensOf "" cs) v

/-- A name of `mv` used other than as a call's head: as a function value. -/
partial def valueUse? (mv : List String) : SExpr → Option (Pos × String)
  | .app _ (.ident _ _) as _ => as.findSome? (valueUse? mv)
  | .ident p n => if mv.contains n then some (p, n) else none
  | e =>
    let kids : List SExpr := match e with
      | .str _ ps => ps.filterMap fun | .code c => some c | _ => none
      | .app _ g as _ => g :: as
      | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x
      | .gen _ _ _ x | .decl _ _ _ _ x => [x]
      | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => [a, b]
      | .cmp _ a r => a :: r.map (·.2)
      | .tuple _ es | .block _ es | .arrayLit _ es | .construct _ _ _ es => es
      | .ite _ cs t e' => cs ++ [t] ++ e'.toList
      | .forE _ cs b => cs ++ [b]
      | .ret _ x => x.toList
      | .caseE _ sc arms => sc :: arms.flatMap fun (pt, v) => pt.toList ++ [v]
      | .mapLit _ kvs => kvs.flatMap fun (k, v) => [k, v]
      | .structDef _ _ fs => fs.filterMap (·.2.2.1)
      | _ => []
    kids.findSome? (valueUse? mv)

/-- A statement where a choice or a call of a function of `mv` (marked) is
    lifted into the body's own clauses: the body then has several values. -/
def liftsHere (c : SExpr) : Bool :=
  match c with
  | .decl _ _ _ _ rhs => hasLiftable rhs
  | .set _ _ _ rhs => hasLiftable rhs
  | .gen _ _ _ src => hasLiftable src
  | e => hasLiftable e

/-- The functions of the program that have several values, inlined at their
    calls (see above); the program unchanged when there are none. -/
def inlineMulti (tops : List STop) : Except String (List STop) := do
  -- (not `Main` or the entry expression, which nothing calls in a failure
  -- context, nor `<suspends>` functions, which cannot run in one)
  let fns : List (String × MFn) := tops.filterMap fun
    | .fn p n ps tps fx r b =>
      if n == "Main" || n == "$Do" || fx.contains "suspends" then none else some (n, ⟨p, ps, tps, fx, r, b⟩)
    | _ => none
  -- (several values, also through the calls of ones that have them, where
  -- the body itself does not take their values)
  let mut mv : List String := []
  let mut changed := true
  while changed do
    changed := false
    for (n, f) in fns do
      let ss := stmtsOf (markCalls mv f.body)
      if !mv.contains n && (hasChoice ss || ss.any liftsHere) then
        mv := mv ++ [n]; changed := true
  if mv.isEmpty then return tops
  let mfs := fns.filter (mv.contains ·.1)
  -- (every name the program binds: parameters, locals, fields, methods)
  let binders : List String := (tops.flatMap fun
    | .fn _ _ ps _ _ _ b => ps.map (·.name) ++ localsOf b
    | .const _ _ _ (.structDef _ _ fs) => fs.map (·.1)
    | .classDef _ _ _ _ _ _ fs _ ms => fs.map (·.1) ++ ms.flatMap fun
        | .fn _ m ps _ _ _ b => m :: ps.map (·.name) ++ localsOf b
        | _ => []
    | _ => []).eraseDups
  -- (the recursive ones, directly or not, and the ones they call: computed
  -- at the call as the array of their values, `F$all`, #235)
  let callees : List (String × List String) := mfs.map fun (n, f) =>
    let used := namesUsed f.body
    (n, mv.filter used.contains)
  -- (whether `g` reaches itself: each function visited once)
  let reaches (g : String) : Bool := Id.run do
    let mut seen : List String := []
    let mut todo := (callees.lookup g).getD []
    let mut found := false
    while !todo.isEmpty && !found do
      let h := todo.head!
      todo := todo.tail!
      if h == g then found := true
      else if !seen.contains h then
        seen := h :: seen
        todo := ((callees.lookup h).getD []) ++ todo
    return found
  let recs := (mfs.filter fun (n, _) => reaches n).map (·.1)
  let mut needAll := recs
  let mut grew := true
  while grew do
    grew := false
    for g in needAll do
      for h in (callees.lookup g).getD [] do
        if !needAll.contains h then needAll := needAll ++ [h]; grew := true
  -- (effect-free: <computes> and no local state; that nothing they may
  -- run prints or calls `Err()` is checked on their Verse Core code, which
  -- shows every call, `checkEager`)
  for g in needAll do
    let some f := mfs.lookup g | continue
    let why (w : String) : String :=
      s!"{f.pos.show}: {g} has several values and is recursive, or called by a recursive one, {w}: such a function must be <computes>, keep no local state, and reach nothing that prints or calls Err(), as all its values are computed at a call (#235)"
    if !f.fx.contains "computes" then throw (why "and it is not <computes>")
    if anyE (fun | .set .. | .decl _ _ _ true _ => true | _ => false) f.body then
      throw (why "and it has a var or a set")
  for (n, f) in mfs do
    if (fns.filter (·.1 == n)).length > 1 then
      throw s!"{f.pos.show}: {n} has several values and is overloaded: such functions are not supported yet (#235)"
    if !f.tparams.isEmpty then
      throw s!"{f.pos.show}: {n} has several values and is generic: such functions are not supported yet (#235)"
    if f.params.any (·.named) then
      throw s!"{f.pos.show}: {n} has several values and named parameters: such functions are not supported yet (#235)"
    if anyE (fun | .ret .. => true | _ => false) f.body then
      throw s!"{f.pos.show}: {n} has several values and a return, which would leave its caller once inlined (#235)"
    if (stmtsOf f.body).any (fun | .app _ (.ident _ "$defer") _ _ => true | _ => false) then
      throw s!"{f.pos.show}: {n} has several values and a defer:, which would run in its caller's clauses once inlined: not supported yet (#235)"
    -- (its body is inlined where other names may be in scope: so neither
    -- its name nor a name its body uses from outside may be bound anywhere)
    if binders.contains n then
      throw s!"{f.pos.show}: {n} has several values, and {n} is also the name of a parameter, local, field or method: rename one, as calls of {n} are inlined (#235)"
    let own := f.params.map (·.name) ++ localsOf f.body
    for u in namesUsed f.body do
      if !recs.contains n && !own.contains u && binders.contains u then
        throw s!"{f.pos.show}: {n} has several values and uses {u}, which is also the name of a parameter, local, field or method: rename one, as {n}'s body is inlined where that name may mean something else (#235)"
  -- (no use as a value)
  let defaults (ps : List SParam) : List SExpr := ps.filterMap (·.default)
  let bodies : List SExpr := tops.flatMap fun
    | .fn _ _ ps _ _ _ b => b :: defaults ps
    | .const _ _ _ e => [e]
    | .classDef _ _ _ _ _ _ fs _ ms => fs.filterMap (·.2.2.1) ++ ms.flatMap fun
        | .fn _ _ ps _ _ _ b => b :: defaults ps
        | _ => []
  for b in bodies do
    if let some (p, n) := valueUse? mv b then
      throw s!"{p.show}: {n} has several values, so it cannot be used as a function value (#235)"
  -- (each call inlined; each function kept for checking only)
  let go (e : SExpr) : StateT Nat (Except String) SExpr := inlineCalls mfs e recs
  let goPs (ps : List SParam) : StateT Nat (Except String) (List SParam) :=
    ps.mapM fun sp => do return { sp with default := ← sp.default.mapM go }
  let (tops', _) ← (tops.filterMapM (m := StateT Nat (Except String)) fun t => do
    match t with
    | .fn p n ps tps fx r b =>
      -- (its own name kept, so that messages name it: nothing calls it)
      if mv.contains n then
        return some (.fn p n ps tps fx r (checkBody b))
      return some (.fn p n (← goPs ps) tps fx r (← go b))
    | .const p n ty e => return some (.const p n ty (← go e))
    | .classDef p n tps sp pa ii fs ov ms =>
      let fs' ← fs.mapM fun (fn, t, d, v) => do return (fn, t, ← d.mapM go, v)
      let ms' ← ms.mapM fun
        | .fn p2 n2 ps2 tps2 fx2 r2 b2 => do return STop.fn p2 n2 (← goPs ps2) tps2 fx2 r2 (← go b2)
        | m => pure m
      return some (.classDef p n tps sp pa ii fs' ov ms')).run 0
  -- (`F$all` for each that needs one: the array of its values)
  let alls : List STop := needAll.filterMap fun g => (mfs.lookup g).map fun f =>
    .fn f.pos s!"{g}$all" f.params f.tparams (f.fx.filter (· != "decides")) (.arr f.ret) (allBody needAll f.ret f.body)
  return tops' ++ alls

end OpenVerse.Front.Choice
