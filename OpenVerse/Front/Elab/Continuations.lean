/- Elaboration continuations; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Context

namespace OpenVerse.Front
open OpenVerse
/-- The names that are values here, for lifting choices (#208): variables
    in scope, `Self` and its fields. -/
def choiceValues (ctx : Ctx) (n : String) : Bool :=
  (ctx.lookup n).isSome || n == "Self" ||
    (match ctx.selfClass with | some c => (ctx.types.fields c).any (·.1 == n) | none => false)

/-- `n.m` reads a field here (a variable or `Self` of a class or struct
    type that has one), for lifting choices: the field is read whole before
    the choice, while a method call's receiver only is (#208). -/
def choiceField (ctx : Ctx) (n m : String) : Bool :=
  let ty? : Option Ty := if n == "Self" then ctx.selfClass.map (fun c => .struct c []) else (ctx.lookup n).map (·.ty)
  match ty? with
  | some (.struct c _) => (ctx.types.fields c).any (·.1 == m)
  | _ => false

/-- Contextual types travel with a lifted operand when a later pass moves
    its clause into a continuation. The metadata has no runtime expressions. -/
def ConstructHint.toExpr (h : ConstructHint) : SExpr :=
  let p := h.pos
  let entries (xs : List (String × Ty)) := xs.map fun (n, t) =>
    SExpr.decl p n (some t.toSTy) false (.tuple p [])
  .app p (.ident p "$constructHint")
    [.str p [.text h.origin], .str p [.text h.frame], .str p [.text h.site],
     .block p (h.defaults.map fun (n, f) => .tuple p [.str p [.text n], .str p [.text f]]),
     .block p (entries h.inputs), .block p (entries h.aliases),
     .decl p "$instance" (some h.ty.toSTy) false (.tuple p [])] false

/-- For `Choice.prepare` (#283): a struct's or class's fields in declaration
    order, the order its constructions evaluate them in, each with whether
    its default is more than a literal. -/
def choiceOrder (ctx : Ctx) (n : String) : Choice.FieldOrder :=
  { fields := if (ctx.types.structs.lookup n).isNone then [] else
      (ctx.types.fields n).map fun (f, _, d) => (f, match d with
        | some d => !Choice.stable (fun _ => true) d
        | none => false)
    probe := ctx.constructProbe, inlineSite := ctx.inlineScopes.headD "",
    origin := ctx.constructOrigin.getD ctx.frameName,
    hints := ((ctx.constructHints.getD []).filter (·.name == n)).map ConstructHint.toExpr }

/-- Lift-generated operand names retain their position and kind between
    the probe and real pass; inserting a default changes their counter only. -/
def constructLocalName (n : String) : String :=
  let suffix := (n.splitOn "@").getLast!
  let parts := suffix.splitOn "_"
  let numeric := fun (s : String) => s.toNat?.isSome
  let lifting := if n.contains '@' then parts.length == 3 && parts.all numeric else
    match parts with
    | [head, col, counter] =>
      numeric col && numeric counter &&
        ["$t", "$c", "$b", "$s", "$dv"].any fun k => head.startsWith k && numeric (head.drop k.length).toString
    | _ => false
  if !lifting then n else String.intercalate "_" (n.splitOn "_").dropLast

def constructHint (ctx : Ctx) (p : Pos) (n site : String) (ty : Ty) : ConstructHint :=
  { pos := p, name := n, site, frame := ctx.frameName,
    origin := ctx.constructOrigin.getD ctx.frameName, defaults := ctx.defaults,
    selfClass := ctx.selfClass, tag := ctx.liftTag,
    inputs := ctx.locals.map fun l => (constructLocalName l.name, l.ty),
    aliases := ctx.types.tvars, ty }

def constructInstance (ctx : Ctx) (p : Pos) (n : String) (ts : List STy) (site : String)
    (origin : String) (metadata : List SExpr) : EM Ty := do
  if !ts.isEmpty || ((ctx.types.sparams.lookup n).getD []).isEmpty then
    return ← resolveTy ctx.types p (if ts.isEmpty then .name n else .app n ts)
  let inputs := ctx.locals.map fun l => (constructLocalName l.name, l.ty)
  let hints := (ctx.constructHints.getD []).filter fun h =>
    h.pos.line == p.line && h.pos.col == p.col && h.pos.file == p.file && h.name == n &&
    h.site == site && h.frame == ctx.frameName && h.origin == origin && h.defaults == ctx.defaults &&
    h.selfClass == ctx.selfClass && h.tag == ctx.liftTag &&
    h.inputs.all (inputs.contains ·) && h.aliases.all (ctx.types.tvars.contains ·)
  let mut tys := (hints.map (·.ty)).eraseDups
  if tys.isEmpty then
    -- A continuation keeps only the lexical values/types its body needs.
    -- Check every retained input against the original instance, and require
    -- one resulting construction type across all compatible candidates.
    for entry in metadata do
      let .app hp (.ident _ "$constructHint")
          [.str _ [.text root], .str _ [.text frame], .str _ [.text active], .block _ defaults,
           .block _ ins, .block _ aliases, .decl _ "$instance" (some ty) _ _] false := entry | continue
      if hp.line != p.line || hp.col != p.col || hp.file != p.file || root != origin || frame != ctx.frameName || active != site then continue
      let ds := defaults.filterMap fun
        | .tuple _ [.str _ [.text c], .str _ [.text f]] => some (c, f)
        | _ => none
      if ds != ctx.defaults then continue
      let check (xs : List SExpr) (available : List (String × Ty)) : EM Bool := do
        for x in xs do
          let .decl _ key (some t) _ _ := x | return false
          let actual := available.filter (·.1 == key) |>.map (·.2)
          if !actual.isEmpty then
            let expected ← resolveTy ctx.types p t
            if !actual.contains expected then return false
        return true
      let candidate ← tryCatch (do
        if !(← check ins inputs) || !(← check aliases ctx.types.tvars) then return none
        return some (← resolveTy ctx.types p ty)) (fun _ => pure none)
      if let some t := candidate then if !tys.contains t then tys := tys ++ [t]
  match tys with
  | [t] => return t
  | [] => eerr p s!"cannot infer the type arguments of {n} before its field choices"
  | _ => eerr p s!"the field choices of {n} have different construction instances here"

/-- Specialize a moved clause's construction metadata before its lexical
    type aliases disappear. Future refining/default scopes keep their own
    records until that scope is lifted. Only lexical names (not normalized
    lifting counters) constrain this transfer; later prefixes add temporaries. -/
def pruneConstructHints (ctx : Ctx) (target : String) (body : SExpr) : SExpr :=
  Choice.mapE (fun
    | .app p (.ident _ "$constructHints") [.block bp entries] false =>
      let entries := entries.filterMap fun entry => match entry with
        | .app hp f [.str op [.text origin], .str sp [.text scope], site,
            .block dp defaults, .block ip inputs, .block ap aliases, result] false =>
          let ds := defaults.filterMap fun
            | .tuple _ [.str _ [.text c], .str _ [.text n]] => some (c, n)
            | _ => none
          if scope != ctx.frameName || ds != ctx.defaults then some entry else
          let agrees (xs : List SExpr) (available : List (String × Ty)) : Bool := xs.all fun
            | .decl q key (some ty) _ _ =>
              let actual := available.filter (·.1 == key) |>.map (·.2)
              if actual.isEmpty then true else
                match (resolveTy ctx.types q ty).run { env := ctx.types } with
                | .ok (t, _) => actual.any fun a =>
                  let a := a.subst ctx.types.tvars
                  !a.params.isEmpty || !t.params.isEmpty || a == t
                | .error _ => true
            | _ => false
          if !agrees inputs (ctx.locals.map fun l => (l.name, l.ty)) || !agrees aliases ctx.types.tvars then none else
            some (.app hp f [.str op [.text origin], .str sp [.text target], site,
              .block dp defaults, .block ip inputs, .block ap aliases, result] false)
        | _ => none
      some (.app p (.ident p "$constructHints") [.block bp entries] false)
    | _ => none) body

/-- Keep a class cast with its branch until its refinement can be applied.
    A receiver bound by earlier clauses need not be in the context yet. -/
def choiceHasCast (ctx : Ctx) (i : SExpr) : Bool :=
  (Choice.arms i).any fun (cs, _) => cs.any fun clauses => clauses.any fun
    | .decl _ _ none false (.app _ (.ident _ target) [_] true) => ctx.types.classes.contains target
    | .decl _ _ none false (.app _ (.ident _ marker) [ .app _ (.ident _ target) [_] true ] false) =>
      ["$methodCast", "$methodCase"].contains marker && ctx.types.classes.contains target
    | _ => false

/-- A generated method dispatch can omit a class that cannot inhabit its
    receiver's current type arguments. Other cases become ordinary refining
    casts, kept with their selected implementation. Receivers are already
    bound once by the dispatch's parameter prefix. -/
partial def pruneMethodCases (ctx : Ctx) : SExpr → SExpr
  | e@(.ite p [.decl dp d none false (.app _ (.ident _ marker)
      [cast@(.app _ (.ident _ target) [.ident _ x] true)] false)] body (some next)) =>
    if !["$methodCast", "$methodCase"].contains marker then e else
    let next := pruneMethodCases ctx next
    let possible := match ctx.lookup x with
      | some l => match l.ty.subst ctx.types.tvars with
        | .struct source args => ((ctx.types.concreteBelow source).filter fun c =>
            if marker == "$methodCase" then c == target else ctx.types.isSub c target).any fun c =>
          ((ctx.types.viewArgs? source c (ctx.types.coreArgs source args) (rigid := false)).bind fun as =>
            ctx.types.refineComparable? [] (ctx.types.comparableArgs c as)).isSome
        | _ => true
      | none => true
    if possible then .ite p [.decl dp d none false cast] body (some next)
    -- A covariant call has an explicit static result type. Drop an exact
    -- class case outside that receiver's domain, including in kept bodies;
    -- synthesizing a failing value here would make a pure checked body fail.
    else if marker == "$methodCase" then next
    -- Keep an if and its unique binder even when it cannot select a body:
    -- later exclusive lowering still needs a case boundary and a known type.
    else .ite p [.decl dp d none false (.block p [.query p (.ident p "false"), .ident p x])]
      (.app p (.ident p "$methodMiss") [] false) (some next)
  | e => e

/-- Normalize a dispatch condition after its receiver prefix is typed. -/
def pruneMethodBinding (ctx : Ctx) : SExpr → SExpr
  | .decl p n ty v (.app q f@(.ident _ "$branchChoice") [i] false) =>
    let i := pruneMethodCases ctx i
    match i with
    | .ite .. => .decl p n ty v (.app q f [i] false)
    | _ => .decl p n ty v i
  | e => e

/-- A local named `n` may be declared here: Verse has no shadowing. -/
def checkNewLocal (ctx : Ctx) (p : Pos) (n : String) : EM Unit := do
  if ctx.lookup n |>.isSome then
    let n := Choice.shownName n
    eerr p s!"'{n}' is already defined; Verse does not allow shadowing (use set {n} = … for a var)"
  -- (nor a soft built-in's: a local cannot hide one, #132)
  if (ctx.sig? n).isSome || builtins.contains n || softBuiltins.contains n then
    eerr p s!"'{n}' is already the name of a function or constant"
  if let some c := ctx.selfClass then
    if (ctx.types.fields c).any (·.1 == n) || ctx.hasMethod c n ||
        ((ctx.types.methodOverloads.lookup n).map (·.any (ctx.hasMethod c ·))).getD false then
      eerr p s!"'{n}' is already a field or method of {c}; Verse does not allow shadowing"

/-- (#335) Whether `e` writes one of the type parameters `tps`: in a written
    type, a construction's, or as a name. Conservative. -/
partial def writesTps (tps : List String) (e : SExpr) : Bool :=
  if tps.isEmpty then false else match e with
  | .app _ (.ident _ "$constructHints") _ false => false
  | e =>
    (match e with
    | .decl _ _ (some t) _ _ => Choice.styMentions tps t
    | .construct _ n ts _ => tps.contains n || ts.any (Choice.styMentions tps)
    | .structDef _ _ _ fs => fs.any fun (_, t, _, _) => Choice.styMentions tps t
    | .refineDef _ _ t _ => Choice.styMentions tps t
    | .ident _ n => tps.contains n
    | _ => false) || e.children.any (writesTps tps)

/-- A helper retains the source context's restrictions and dependency stack,
    while its generated control flow still owns its own loops and exits. -/
def sourceContextOf (ctx : Ctx) : Choice.SourceContext := {
  inCtor := ctx.inCtor, inParamDefault := ctx.inParamDefault,
  inBlock := ctx.inBlock, inDefer := ctx.inDefer,
  inDefaultCheck := ctx.inDefaultCheck, inRepeat := ctx.inRepeat,
  inChoice := ctx.inChoice, inArm := ctx.inArm, inBranch := ctx.inBranch,
  defaults := ctx.defaults }

def sourceContextKey (ctx : Ctx) : String :=
  let scope := sourceContextOf ctx
  let source := if scope == ({} : Choice.SourceContext) then "" else "_source:" ++ reprStr scope
  source ++ (if ctx.choiceCoercions.isEmpty then "" else "_conversions:" ++
    reprStr (ctx.choiceCoercions.map fun (dictionary, source, target) => (dictionary.name, source, target)))

/-- Refined helpers keep their source copy tag and context identity separate. -/
def refineTagOf (ctx : Ctx) : String :=
  let source := sourceContextKey ctx
  let inputs := ctx.locals.filterMap fun l =>
    if (Choice.shownName l.name).startsWith "$" then none else some (l.name, l.ty, l.mutable)
  let typing := reprStr (ctx.types.tvars, inputs, ctx.retTy, ctx.inlineScopes)
  ctx.refineScope ++ ctx.liftTag ++ (if source.isEmpty then "" else s!"$source{(source ++ typing).hash}")

def firstReturns (rest : List SExpr) : Bool :=
  (Refine.findPart (fun | .ret .. => true | _ => false) false (.block { line := 0, col := 0 } rest)).isSome

/-- The source return type remains separate from a helper's packet type. -/
def firstReturnType (ctx : Ctx) : STy :=
  let ty := match ctx.refineExits.ret with
    | some (some (_, ty), _) => ty
    | some (none, _) => .name "void"
    | none => match ctx.forReturnSlot.bind ctx.lookup with
      | some { ty := .opt t, .. } => t.toSTy
      | _ => ctx.retTy.toSTy
  ty.substNames (ctx.types.tvars.map fun (n, t) => (n, t.toSTy))

def firstReturnKey (ctx : Ctx) (rest : List SExpr) : String :=
  if !firstReturns rest then "" else
    let ty := firstReturnType ctx
    let bounds := Ty.mergeParamBounds ((ctx.types.tvars.map (·.2)).flatMap Ty.paramsC)
      |>.filter fun (n, _) => Choice.styMentions [n] ty
    "_return:" ++ reprStr (ty, bounds)

/-- Normal success has all bound names. A return instead has the saved
    operand; both outcomes copy back captures before the caller proceeds. -/
def firstResult (p : Pos) (name : String) (binds sets : List Local) (source : Option Ty) :
    STy × SExpr × Option Choice.FirstReturn :=
  let values := binds.map fun l => SExpr.ident p l.name
  let copied := sets.map fun l => SExpr.ident p l.name
  match source with
  | none => (.tup ((binds ++ sets).map (·.ty.toSTy) ++ [.name "logic"]),
      .tuple p (values ++ copied ++ [.ident p "true"]), none)
  | some ty =>
    let ret := STy.tup (.opt (.tup (binds.map (·.ty.toSTy))) :: sets.map (·.ty.toSTy) ++ [.opt ty.toSTy, .name "logic"])
    let value := if ty == .void then none else some (name ++ "$return")
    let saved := (value.map (SExpr.ident p ·)).getD (.tuple p [])
    let normal := SExpr.tuple p (.optionLit p (.tuple p values) :: copied ++ [.ident p "false", .ident p "true"])
    let normal := SExpr.decl p (name ++ "$normal") (some ret) false normal
    let returned := SExpr.tuple p (.ident p "false" :: copied ++ [.optionLit p saved, .ident p "true"])
    (ret, normal, some { ty := ty.toSTy, value, packet := [returned] })

/-- Infer the callee's actual type arguments before joining its result.
    An expected result type must not widen the input's instance first. -/
def continuationBind (p : Pos) (lift : Choice.FirstLift) (name : String) (call : SExpr) : List SExpr :=
  match lift.joinedRet with
  | none => [.decl p name none false call]
  | some ty =>
    let raw := name ++ "$instance"
    [.decl p raw none false call, .decl p name (some ty) false (.ident p raw)]

/-- Update source captures before returning or exposing the normal bindings. -/
def firstUnpack (p : Pos) (l : Choice.FirstLift) (packet : String) : List SExpr :=
  let get (base : String) (j : Nat) := SExpr.app p (.ident p base) [.int p (j : Int)] false
  if l.returnExit.isNone then
    l.binds.zipIdx.map (fun (n, i) => .decl p n none (l.varBinds.contains n) (get packet i)) ++
      l.sets.zipIdx.map (fun (n, j) => .set p (.ident p n) none (get packet (l.binds.length + j)))
  else
    let returned := packet ++ "$returned"
    let normal := packet ++ "$normal"
    l.sets.zipIdx.map (fun (n, j) => .set p (.ident p n) none (get packet (j + 1))) ++
      [.ite p [.decl p returned none false (.query p (get packet (l.sets.length + 1)))]
        (.ret p (some (.ident p returned))) none,
        .decl p normal none false (.query p (get packet 0))] ++
      l.binds.zipIdx.map (fun (n, j) => .decl p n none (l.varBinds.contains n) (get normal j))

/-- A lazy helper owns its producer and the complete prepared suffix. That
    suffix changes when a composed choice is replaced by a continuation call;
    source position and captured names alone would reuse the previous contract.
    The named type instances also distinguish an inlined body's output types
    even when its producer parameters and captures have identical types. -/
def Ctx.choiceCoercionScope (ctx : Ctx) : Ctx :=
  if ctx.choiceCoercions.isEmpty then ctx else
  let dictionaries := (ctx.choiceCoercions.map (·.1)).filter fun dictionary =>
    !(ctx.locals.any (·.name == dictionary.name))
  let variables := Ty.mergeParamBounds (ctx.choiceCoercions.flatMap fun (_, source, target) => source.paramsC ++ target.paramsC)
  let missing := variables.filter fun (name, _) => !(ctx.types.tvars.any (·.1 == name))
  { ctx with
    locals := dictionaries ++ ctx.locals,
    types := { ctx.types with tvars := ctx.types.tvars ++ missing.map (fun (name, bound) => (name, Ty.param name bound)) } }

def Ctx.choiceCoercionBody (ctx : Ctx) (body : SExpr) : SExpr :=
  if ctx.choiceCoercions.isEmpty then body else
  let p := body.pos
  .app p (.ident p "$choiceCoercions") [.block p (ctx.choiceCoercions.map fun (dictionary, source, target) =>
    .tuple p [.ident p dictionary.name, .construct p "$choiceConversion" [source.toSTy, target.toSTy] []]), body] false

def firstKey (ctx : Ctx) (p : Pos) (lp : List SExpr) (b : String) (bty : Option STy)
    (rest : List SExpr) : String :=
  let written := SExpr.block p (lp ++ rest)
  let inputs := (Choice.namesUsed written).eraseDups.filterMap fun n =>
    (ctx.lookup n).map fun l => (n, l.ty, l.mutable)
  let aliases := ctx.types.tvars.filter fun (n, _) =>
    writesTps [n] written || ((bty.map (Choice.styMentions [n])).getD false)
  reprStr (p, b, bty, lp, rest, inputs, aliases, ctx.selfClass, ctx.liftTag, ctx.inlineScopes) ++ sourceContextKey ctx ++ firstReturnKey ctx rest

/-- A cast `T[X]`, `X` of type `xty`, that holds only under a refinement of
    the code's type parameters (#243): `T` fixes or repeats type arguments
    of `X`'s class, which agree with `X`'s only when they are unified (as
    `elabCast` refuses). `X`'s class and type arguments, `T`'s type
    arguments, the classes the cast tests for, and the equations of the
    refinement; `none` for any other cast. -/
def refiningCast? (env : TyEnv) (T : String) (xty : Ty) (avoid : List String := []) :
    Option (String × List Ty × List Ty × List String × List (Ty × Ty) × List (String × String × Bool)) := do
  let .struct S sargs := xty | none
  if !env.classes.contains S || !env.classes.contains T then none
  if (env.sparams.lookup T).isNone && (env.coreArgs T []).isEmpty then none
  if !(env.isSub S T || env.isSub T S) then none
  let rargs := env.coreArgs S sargs
  let common := (env.concreteBelow S).filter (env.isSub · T)
  if common.isEmpty then none
  let tv := env.coreVars T
  -- (#351: an object referred to through views relates its type arguments
  -- to `T`'s through `S`'s view of `T`, never by position)
  let viewedS := env.viewed.contains S
  if !viewedS && tv.length == rargs.length && tv.all (fun (v, _) => !v.startsWith "$arg") then
    -- (#243: `T`'s Verse Core type arguments are its own type parameters,
    -- as many as the object's: those, as the object's type gives them)
    let targs := if env.isSub S T then env.upArgs S sargs T else env.argsBelow S sargs T
    let cargs := env.coreArgs T targs
    let bounds := env.refineComparable? [] (env.comparableArgs T targs)
    if bounds.isNone then none else
    if cargs == rargs && bounds.any List.isEmpty then none
    let eqs := rargs.zip cargs
    if (Ty.unifyEqs (fun _ _ => none) [] eqs).isNone then none
    some (S, sargs, targs, common, eqs, [])
  else
    -- (#250: more, or not its type parameters as a whole: each of `T`'s
    -- type parameters fresh (not a name of `avoid`), unified with the
    -- object's type arguments, the fresh ones bound first; those left
    -- unbound are opened, as comparable as the parameters they stand for)
    if env.isSub S T then none
    let ps := (env.sparams.lookup T).getD []
    let names : List String := ps.foldl (fun acc (v, _) => Id.run do
      let mut n := v ++ "'"
      while avoid.contains n || acc.contains n do n := n ++ "'"
      return acc ++ [n]) []
    let targs := (ps.zip names).map fun ((_, c), n) => Ty.param n c
    let cargs := env.coreArgs T targs
    if !viewedS && cargs.length < rargs.length then none
    let eqs := if viewedS then (env.viewOf S T cargs).zip rargs
      else (cargs.take rargs.length).zip rargs
    let some μ := Ty.unifyEqs (fun _ _ => none) [] eqs | none
    let opened := (ps.zip names).filterMap fun ((v, c), n) =>
      if (μ.lookup n).isSome then none else some (n, v, c)
    -- (an interface has no hidden fields to read opened ones from, #53:
    -- such a cast is a plain one, which refuses unknown type arguments)
    if (env.info T).isIface && !opened.isEmpty then none
    -- (nothing to refine, to open, nor past the object's: a plain cast;
    -- through a view, the object's type arguments come from the dispatch,
    -- as a plain cast does not give them, #351)
    let bounds := env.refineComparable? μ (env.comparableArgs T targs)
    if bounds.isNone then none else
    if !viewedS && cargs.length == rargs.length && opened.isEmpty && μ.all (names.contains ·.1) &&
        (bounds.getD []).all (names.contains ·.1) then none
    some (S, sargs, targs, common, eqs, opened)

/-- Unify a refining cast's equations, preserving comparable opened types. -/
def castRefinement? (env : TyEnv) (eqs : List (Ty × Ty)) (opened : List (String × String × Bool))
    (required : List Ty := []) :
    Option (List (String × Ty) × List (String × String × Bool)) := do
  let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
    if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
  let μ ← Ty.unifyEqs coreFields [] eqs
  let μ ← env.refineComparable? μ required
  let opened := opened.map fun (n, v, cmp) =>
    let refined := (Ty.param n cmp).subst μ
    (n, v, cmp || refined.comparable env)
  some (μ, opened)

/-- The implementation `(super:)M` reaches in a method of class `c`: what
    the class inherits for the method's slot (`(r:)M`'s, or every slot of
    `M`, implemented alike above it, or the class chain's). -/
def superImpl (ctx : Ctx) (p : Pos) (c m : String) : EM String := do
  -- in `(r:)m`, slot r; otherwise every slot of `m` (#70): what is above `c`
  -- implements them alike, or the class chain's implementation is the one
  let slots := match ctx.selfMethod with
    | some cur => match (cur.drop 1).toString.splitOn ":)" with
      | [r, m'] => if cur.startsWith "(" && m' == m then [r] else ctx.rootsOf c m
      | _ => ctx.rootsOf c m
    | none => ctx.rootsOf c m
  let ups := (ctx.types.supers c).drop 1
  let found := (slots.filterMap fun r => (ctx.types.slotImpls (ctx.implAt r m) ups r).head?).eraseDups
  let inClass := found.filter fun f => !(ctx.types.info ((f.splitOn ".").head!)).isIface
  match found, inClass with
  | [f], _ => pure f
  | [], _ => eerr p s!"nothing above {c} implements '{m}'"
  | _, [f] => pure f
  | f :: g :: _, _ =>
    eerr p s!"(super:){m} is ambiguous here: {f} and {g} implement it for different interfaces above {c}; call it from a qualified (i:){m}"

/-- What, in the branch of a cast that refines type arguments, would not
    mean the same once the branch is a function of its own (#243): its
    position and what it is. `muts` are the `var`s it uses from outside. -/
def refineBranchWhy? (_ctx : Ctx) (_p : Pos) (body : SExpr) (muts : List String) (allowEsc : Bool := false) :
    Option (Pos × String) :=
  if let some e := (if allowEsc then none else Refine.findPart (fun | .ret .. => true | _ => false) false body) then
    some (e.pos, "it cannot have a return yet")
  else if let some e := (if allowEsc then none else Refine.findPart (fun | .brk _ => true | _ => false) true body) then
    some (e.pos, "it cannot have a break that leaves it yet")
  else if let some e := Refine.findPart (fun
      | .set _ l _ _ => (Choice.rootName? l).any muts.contains
      | _ => false) false body then
    some (e.pos, "it cannot set a var from outside it yet")
  else none

/-- Statements every path of which ends in a `return` or a `break` (#243). -/
partial def escapesAlways (ss : List SExpr) : Bool :=
  match ss.getLast? with
  | some (.ret ..) => true
  | some (.ite _ _ t (some u)) => escapesAlways (Choice.stmtsOf t) && escapesAlways (Choice.stmtsOf u)
  | e => e.any Refine.isBreak

/-- How a refined branch's value leaves its function (#243): not at all
    (the `if` is `void`), as it is (at its type when known: the branch
    always ends), as an option (it may also leave by a `return` or
    `break`), or not, the branch always leaving, so the `else`'s value is
    taken after the `if`. -/
inductive ExitVal where
  | none
  | raw (t : Option STy)
  | opt (t : STy)
  | elseAfter

/-- (#243) `if (D := T[x]) then B else E` whose branch `B`, compiled as a
    function of its own, sets `var`s from outside it (`vars`), has a
    `return`, or a `break` that leaves it: every way it leaves becomes a
    value of a tuple of what it says (an option of the enclosing
    function's result, `retS`, or a `logic` for a `void` one; a `logic`
    for a `break`; its value, as `vm` has it) and the values of copies of
    those `var`s (`$exit…'N`, shown as written), which it uses in their
    place; the `else` gives the `var`s' own. After the `if`, the caller
    sets the `var`s from the tuple, then returns or breaks as it says, else
    takes the value. Each value is bound, at its type, before it goes in an
    option, so that its failure is the branch's. Gives the new branch and
    else, the tuple's type when known, the name the `if`'s value is bound
    to, what follows it, and how the lifted function packs explicit exits. -/
def refineExits (p : Pos) (body : SExpr) (elseE : Option SExpr) (vars : List (String × STy))
    (hasRet : Bool) (brkPart : Option SExpr) (retS : Option STy) (vm : ExitVal) :
    SExpr × SExpr × Option STy × String × List SExpr × Refine.Exits :=
  let tag := s!"$exit{p.line}_{p.col}"
  let cp (n : String) : String := s!"{tag}'{n}"
  let ren := vars.map fun (n, _) => (n, cp n)
  let hasBrk := brkPart.isSome
  let retC : List STy := if hasRet then [retS.map STy.opt |>.getD (.name "logic")] else []
  let brkC : List STy := if hasBrk then [.name "logic"] else []
  let valC : List (Option STy) := match vm with
    | .raw t => [t]
    | .opt t => [some (.opt t)]
    | _ => []
  let comps : List (Option STy) := (retC ++ brkC).map some ++ valC ++ vars.map (some ·.2)
  let tupS : Option STy := if comps.all (·.isSome) then
      some (match comps.filterMap id with | [c] => c | cs => .tup cs) else none
  let n := comps.length
  let rr := s!"{tag}'r"
  let rx := s!"{tag}'rx"
  let vx := s!"{tag}'vx"
  let mk (retV : List SExpr) (brk : Bool) (val? : Option SExpr) (varsV : List SExpr) : List SExpr :=
    let brkV : List SExpr := if hasBrk then [.ident p (if brk then "true" else "false")] else []
    let (pre, valV) : List SExpr × List SExpr := match vm, val? with
      | .raw t, some v => ([.decl p vx t false v], [.ident p vx])
      | .opt t, some v => ([.decl p vx (some t) false v], [.optionLit p (.block p [.ident p vx])])
      | .opt _, none => ([], [.ident p "false"])
      | .raw _, none => ([], [.tuple p []])
      | _, _ => ([], [])
    let val := match retV ++ brkV ++ valV ++ varsV with | [v] => v | vs => .tuple p vs
    pre ++ [.decl p rr tupS false val, .ident p rr]
  let copiesV := vars.map fun (n, _) => SExpr.ident p (cp n)
  let outsV := vars.map fun (n, _) => SExpr.ident p n
  let copies := vars.map fun (n, t) => SExpr.decl p (cp n) (some t) true
    (.app p (.ident p "$refineCopyIn") [.ident p n] false)
  let noRet : List SExpr := if hasRet then [.ident p "false"] else []
  let done (val? : Option SExpr) (varsV : List SExpr) := SExpr.block p (mk noRet false val? varsV)
  let exits : Refine.Exits := {
    ret := if hasRet then
      let v := if retS.isSome then SExpr.optionLit p (.block p [.ident p rx]) else .ident p "true"
      some (retS.map (rx, ·), mk [v] false none copiesV) else none
    brk := if hasBrk then some (mk noRet true none copiesV) else none }
  let always := escapesAlways (Choice.stmtsOf body)
  let body := Choice.renameE ren body
  -- Mark breaks that leave this lift. A nested lift forwards the marker
  -- after copying back into this frame, just as it forwards a return.
  let body := Choice.mapE (fun
    | .brk q => some (Refine.liftedBreak q)
    | l@(.loop ..) => some l
    | _ => none) body
  let ss := Choice.stmtsOf body
  let (stmts, value) : List SExpr × Option SExpr := match vm, ss.getLast? with
    | .raw _, some (.decl q y _ _ _) | .opt _, some (.decl q y _ _ _) => (ss, some (.ident q y))
    | .raw _, some l | .opt _, some l => (ss.dropLast, some l)
    | _, _ => (ss, none)
  let hasDefer := ss.any fun
    | .app _ (.ident _ "$defer") [_] false => true
    | _ => false
  let endV : List SExpr :=
    if always then ss
    else if vars.isEmpty || !hasDefer then stmts ++ [done value copiesV]
    -- Leave the scope of the branch's defers before reading the copied slots.
    -- A branch value is evaluated inside that scope and saved across cleanup.
    else match value with
      | some v => [done (some (.block p (stmts ++ [v]))) copiesV]
      | none => [.block p stmts, done none copiesV]
  let thenB := SExpr.block p (copies ++ endV)
  let elseB : SExpr := match vm, elseE with
    | .raw _, some e | .opt _, some e => done (some e) outsV
    | .none, some e => .block p [e, done none outsV]
    | _, _ => done none outsV
  let t := s!"{tag}'t"
  let get (i : Nat) : SExpr := if n == 1 then .ident p t else .app p (.ident p t) [.int p (i : Int)] false
  let nRB := retC.length + brkC.length
  let ci := nRB + valC.length
  let rv := s!"{tag}'rv"
  let vv := s!"{tag}'vv"
  let brk := match brkPart with
    | some (.brk _) | none => SExpr.brk p
    | some _ => Refine.liftedBreak p
  let writes := vars.zipIdx.map fun ((nm, _), k) => SExpr.set p (.ident p nm) none
    (.app p (.ident p "$refineCopyOut") [get (ci + k)] false)
  let after : List SExpr := writes ++
    (if hasRet then [if retS.isSome then .ite p [.decl p rv none false (.query p (get 0))] (.ret p (some (.ident p rv))) none
      else .ite p [.query p (get 0)] (.ret p none) none] else []) ++
    (if hasBrk then [.ite p [.query p (get retC.length)] brk none] else []) ++
    [match vm, elseE with
      | .raw _, _ => get nRB
      | .opt _, _ => .ite p [.decl p vv none false (.query p (get nRB))] (.ident p vv) (some (.app p (.ident p "Err") [] false))
      | .elseAfter, some e => e
      | _, _ => .tuple p []]
  (thenB, elseB, tupS, t, after, exits)

/-- In a method of class `c`, the branch of a cast that refines (#243), with
    the members of `Self` it names bare (its fields and methods, not shadowed
    by a local) made `Self.member`, as the elaborator reads them: its
    function, of its own, takes `Self` as a parameter. A super call keeps
    its source method's lookup scope, including qualified slots and
    overload resolution, and explicitly captures `Self`. -/
partial def selfQualify (ctx : Ctx) (c : String) (e : SExpr) : SExpr :=
  let isMethod (n : String) : Bool := ctx.hasMethod c n ||
    ((ctx.types.methodOverloads.lookup n).map (·.any (ctx.hasMethod c ·))).getD false
  let isField (n : String) : Bool := (ctx.types.fields c).any (·.1 == n)
  let bound := Choice.localsOf e
  let free (n : String) : Bool := (ctx.lookup n).isNone && !bound.contains n && n != "Self"
  Choice.mapE (fun
    | e@(.app _ (.ident _ "$sourceSuper") _ false) => some e
    | .app p f@(.member _ (.ident _ "(super:)") _) args br =>
      some (.app p (.ident p "$sourceSuper")
        [.str p [.text c], .str p [.text (ctx.selfMethod.getD "")], .ident p "Self",
          .app p f (args.map (selfQualify ctx c)) br] false)
    | e@(.member p (.ident _ "(super:)") _) =>
      some (.app p (.ident p "$sourceSuper")
        [.str p [.text c], .str p [.text (ctx.selfMethod.getD "")], .ident p "Self", e] false)
    | .app p (.ident q n) args br =>
      if free n && (isMethod n || (isField n && !builtins.contains n && !softBuiltins.contains n)) then
        some (.app p (.member q (.ident q "Self") n) (args.map (selfQualify ctx c)) br)
      -- (a call of anything else keeps its head as written: a field named
      -- like a built-in, `Max(7, 3)`, is the built-in there, as elsewhere)
      else some (.app p (.ident q n) (args.map (selfQualify ctx c)) br)
    | .ident p n => if free n && (isField n || isMethod n) then some (.member p (.ident p "Self") n) else none
    | _ => none) e

/-- A continuation keeps the parameters of its inputs, results and written
    types. A parameter not determined by its inputs takes an explicit witness,
    so a type used only by a local annotation is still inferred at the call. -/
def contTypes (ctx : Ctx) (p : Pos) (inputs outputs : List Ty) (written : SExpr) :
    Except String (List TParam × List SParam × List SExpr) := do
  let inputTps := inputs.flatMap Ty.paramsC
  let writtenTys := ctx.types.tvars.filterMap fun (n, t) =>
    if writesTps [n] written then some t else none
  let tps := Ty.mergeParamBounds (inputTps ++ (outputs ++ writtenTys).flatMap Ty.paramsC)
  let extra := tps.filter fun (n, _) => !inputTps.any (·.1 == n)
  let available := (ctx.types.tvars.map (·.2)).flatMap Ty.paramsC
  if extra.any (fun (n, _) => !available.any (·.1 == n)) then
    throw "a continuation type parameter has no witness in this context"
  return (tps.map (fun (n, cmp) => { pos := p, name := n, constraint := if cmp then "comparable" else "type" }),
    extra.map (fun (n, _) => { name := s!"$type{n}", ty := .name n }),
    extra.map (fun (n, _) => .app p (.ident p "$witness") [.ident p n] false))

/-- (#246) The function of its own a lazily taken call where the first
    success is taken is compiled as, when what it runs once for all the
    values of an item has effects (`Choice.FirstLift`): from the call
    (`lp`, its binding `b`), the consumer's names before it (`ctx`) and
    after the clauses that follow it (`c2`, those clauses `rest`), and the
    effects all that has (`fxB`); or why it cannot be yet. -/
def firstLiftOf (ctx c2 : Ctx) (p : Pos) (g : String) (lp : List SExpr) (b : String) (bty : Option STy)
    (rest : List SExpr) (fxB : List (String × Pos × Option String)) (suspends : Bool) (vty : Ty)
    (instances : List (String × List (String × Ty)) := []) :
    Except String Choice.FirstLift := do
  let ctx := ctx.choiceCoercionScope
  let [_, .block _ ps, .block _ cls, .decl _ _ _ _ tail] := lp | throw "internal: a $loop marker"
  let key := firstKey ctx p lp b bty rest
  let written := SExpr.block p (lp ++ rest)
  -- Written types use the context's current instances, including inlined
  -- producer parameters and aliases from an enclosing refining cast.
  let σt := ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let bty := bty.map (·.substNames σt)
  let cls := cls.map (Refine.substTypes σt)
  let tail := Refine.substTypes σt tail
  let rest := rest.map (Refine.substTypes σt)
  -- (in a method: the members of `Self` the clauses name bare, as members
  -- of `Self`, which the function takes as a parameter, as #243's do)
  let rest ← match ctx.selfClass with
    | some c =>
      pure (rest.map (selfQualify ctx c))
    | none => pure rest
  -- (a `return`, or a `break` that leaves them, would leave the function
  -- of its own, not the consumer's)
  let source ← if firstReturns rest then
      some <$> (resolveTy ctx.types p (firstReturnType ctx)).run' { env := ctx.types }
    else pure none
  if (Refine.findPart (fun | .brk _ => true | _ => false) true (.block p rest)).isSome then
    throw "where the clauses after it have a break that leaves them"
  if suspends then throw "as the clauses after it suspend"
  let pnames := ps.filterMap fun | .ident _ n => some n | _ => none
  let pls ← pnames.mapM fun n => match ctx.lookup n with
    | some l => pure l
    | none => throw s!"internal: parameter {n}"
  -- (the consumer's names the clauses after it use, in order of first use)
  let caps : List Local := (Choice.namesUsed (ctx.choiceCoercionBody (.block p rest))).eraseDups.filterMap fun n =>
    if pnames.contains n then none else ctx.lookup n
  let setNames := Choice.setsIn (.block p rest)
  let sets := caps.filter fun l => l.mutable && setNames.contains l.name
  -- (its own binding too: a call in the clauses of another such call's
  -- function, compiled as one too, binds only what that one gives)
  let binds := (b :: Choice.boundIn rest).eraseDups
  let bls ← binds.mapM fun n => match c2.lookup n with
    | some l => pure l
    | none => throw s!"internal: name {n}"
  let (tps, typeParams, typeArgs) ← contTypes ctx p ((pls ++ caps).map (·.ty))
    (vty :: bls.map (·.ty) ++ source.toList) written
  -- A type determined by the entry's inputs may be absent from another
  -- member's inputs. Every member must still infer the shared helper's
  -- type parameters, including those used only by a producer result.
  let memberInputs := instances.filterMap fun (h, σ) =>
    if h == g then none else (ctx.sig? h).map fun sig =>
      (sig.params.map (·.subst σ) ++ caps.map (·.ty)).flatMap Ty.params
  let missing := tps.filter fun tp => memberInputs.any (!·.contains tp.name) &&
    !typeParams.any (·.name == s!"$type{tp.name}")
  let typeParams := typeParams ++ missing.map (fun tp => ({ name := s!"$type{tp.name}", ty := .name tp.name } : SParam))
  let typeArgs := typeArgs ++ missing.map (fun tp => SExpr.app p (.ident p "$witness") [.ident p tp.name] false)
  let name := s!"$first{p.line}_{p.col}_{key.hash}" ++ (if p.file.isEmpty then "" else s!"_{p.file}")
  -- Every recursive edge, including a mutual member's, forwards the same
  -- witnesses; a type used only by the suffix has no producer argument.
  let capArgs := caps.map (fun l => SExpr.ident p l.name) ++ typeParams.map (fun sp => .ident p sp.name)
  -- (#283) a function of a strongly connected group: the others' too, one
  -- function each, named after this one's
  let (tail, members) : SExpr × List SExpr := match tail with
    | .app _ (.ident _ "$group") (t0 :: ms) false => (t0, ms)
    | t => (t, [])
  let mnames : List String := members.filterMap fun
    | .app _ (.ident _ "$member") (.ident _ h :: _) false => some h
    | _ => none
  let nameOf (h : String) : String := if h == g then name else s!"{name}_{h.replace "::" "_"}"
  let heap := ["reads", "writes", "allocates"].filter fun k =>
    fxB.any (·.1 == k) || ((g :: mnames).any fun h => ((ctx.sig? h).map (·.fx.contains k)).getD false)
  let capPs : List SParam :=
    caps.map fun l => { name := if sets.any (·.name == l.name) then s!"{l.name}$in" else l.name, ty := l.ty.toSTy }
  let params : List SParam := pls.map (fun l => { name := l.name, ty := l.ty.toSTy }) ++ capPs
  let specs := (if heap.isEmpty then ["computes"] else heap) ++ ["decides"]
  let (ret, normal, returnExit) := firstResult p name bls sets source
  let setsT := sets.map fun l => (l.name, l.ty.toSTy)
  let recArgs (target : Option String) (q : Pos) (as : List SExpr) : List SExpr × List SExpr :=
    let h := target.getD g
    match ctx.sig? h with
    | some s =>
      let tys := if h == g then pls.map (·.ty) else s.params.map (·.subst ((instances.lookup h).getD []))
      let named := as.any fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
      if s.named.isEmpty && !named && as.length == tys.length then ([], as) else
      let n := s!"$recursiveArgs{q.line}_{q.col}"
      let types := ((instances.lookup h).getD []).map fun (n, t) =>
        SExpr.decl q n (some t.toSTy) false (.tuple q [])
      ([.decl q n (some (.tup (tys.map Ty.toSTy))) false
          (.app q (.ident q "$callArgs") [.ident q h, .block q as, .block q types] false)],
        tys.zipIdx.map fun (_, j) => .app q (.ident q n) [.int q (j : Int)] false)
    | none => ([], as)
  let extraFns ← members.mapM fun
    | .app _ (.ident _ "$member") [.ident _ h, .block _ hps, .block _ hcls, .decl _ _ _ _ htail] false => do
      let some sig := ctx.sig? h | throw s!"internal: no signature for {h} (#283)"
      let σ := (instances.lookup h).getD []
      let aliases := σ.map fun (n, t) => (Choice.memberTypeName h n, t.toSTy)
      let hcls := hcls.map (Refine.substTypes aliases)
      let htail := Refine.substTypes aliases htail
      let hparams : List SParam ← (hps.zip (sig.params.map (·.subst σ))).mapM fun
        | (.ident _ n, t) => pure { name := n, ty := t.toSTy }
        | _ => throw "internal: a $member parameter (#283)"
      let body := Choice.firstBody (nameOf h) p b bty hcls htail rest binds setsT capArgs (some vty.toSTy) nameOf
        (fun target => recArgs (some (target.getD h))) (if source.isSome then some normal else none)
      pure (STop.fn p (nameOf h) (hparams ++ capPs ++ typeParams) tps specs ret
        (pruneConstructHints ctx (nameOf h) body))
    | _ => throw "internal: a $member (#283)"
  return { key, pos := p, name, returnExit, sourceContext := sourceContextOf ctx, inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
           params := params ++ typeParams, tparams := tps, specs, ret,
           body := ctx.choiceCoercionBody <| pruneConstructHints ctx name
             (Choice.firstBody name p b bty cls tail rest binds setsT capArgs (some vty.toSTy) nameOf recArgs
               (if source.isSome then some normal else none)),
           binds, sets := sets.map (·.name), args := pnames.map (SExpr.ident p ·) ++ caps.map (fun l => .ident p l.name) ++ typeArgs,
           varBinds := (bls.filter (·.mutable)).map (·.name), extraFns }

/-- (#335) The key of a continuation: where the composed choice is, its
    binding, and the consumer's names the clauses after it use (in a method,
    once its members are `Self`'s, as in the function), as `firstKey`. -/
def contKey (ctx : Ctx) (p : Pos) (b : String) (rest : List SExpr) : String :=
  let rest := match ctx.selfClass with
    | some c => rest.map (selfQualify ctx c)
    | none => rest
  -- (with their types: a `for`'s body copied once per alternative of a
  -- choice has the same place, with names of other types)
  let caps := (Choice.namesUsed (.block p rest)).eraseDups.filterMap fun n =>
    (ctx.lookup n).map fun l => s!"{n}:{reprStr l.ty}"
  -- A type used only by a written annotation has no captured value. Its
  -- instance still distinguishes helpers made at a shared source position.
  let written := ctx.types.tvars.filterMap fun (n, t) =>
    if writesTps [n] (.block p rest) then some s!"{n}:{reprStr t}" else none
  let typed := if written.isEmpty then "" else "_types:" ++ String.intercalate "," written
  -- (and the places of the clauses after it: the same choice, inside an
  -- alternative of another one with a continuation, has the call of that
  -- one after it in the next elaboration, which may use the same names)
  let places := rest.map fun c => s!"{c.pos.line}.{c.pos.col}"
  s!"k{p.line}_{p.col}_{p.file}_{b}_{String.intercalate "," caps}_{String.intercalate "," places}{typed}{ctx.liftTag}{reprStr ctx.inlineScopes}{sourceContextKey ctx}"

/-- (#335) The function of its own that the clauses after a composed choice
    (#296) are compiled as, where the first success is taken and those
    clauses (`rest`) have another such choice: called from each alternative
    with its value (`b`) and the consumer's names `rest` uses (from `ctx`,
    before the choice), it gives at the first success of `rest` the names
    they bind and the final values of the `var`s they set (their types from
    `c2`, after `rest`; `fxB`, the effects). So `rest` is compiled once, not
    once per alternative, which doubled the code with each such choice. Or
    why not, and the clauses are copied, as before. -/
def contLiftOf (ctx c2 : Ctx) (p : Pos) (b : String) (alts rest : List SExpr)
    (fxB : List (String × Pos × Option String)) : Except String Choice.FirstLift := do
  let ctx := ctx.choiceCoercionScope
  let written := ctx.choiceCoercionBody (.block p rest)
  -- (the alternatives' names too: their types fix the binding's)
  let key := contKey ctx p b (alts ++ rest) ++ firstReturnKey ctx rest
  let σt := ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let rest := rest.map (Refine.substTypes σt)
  -- (in a method: the members of `Self` the clauses name bare, as members
  -- of `Self`, which the function takes as a parameter, as #279's do)
  let rest ← match ctx.selfClass with
    | some c =>
      pure (rest.map (selfQualify ctx c))
    | none => pure rest
  -- (a `return`, or a `break` that leaves them, would leave the function)
  let source ← if firstReturns rest then
      some <$> (resolveTy ctx.types p (firstReturnType ctx)).run' { env := ctx.types }
    else pure none
  if (Refine.findPart (fun | .brk _ => true | _ => false) true (.block p rest)).isSome then throw "a break"
  let caps : List Local := (Choice.namesUsed (ctx.choiceCoercionBody (.block p rest))).eraseDups.filterMap ctx.lookup
  let setNames := Choice.setsIn (.block p rest)
  let sets := caps.filter fun l => l.mutable && setNames.contains l.name
  let binds := (b :: Choice.boundIn rest).eraseDups
  let bls ← binds.mapM fun n => match c2.lookup n with
    | some l => pure l
    | none => throw s!"internal: name {n}"
  let some bl := bls.head? | throw "internal: no binding"
  if bl.mutable then throw "a var binding"
  let (tps, typeParams, typeArgs) ← contTypes ctx p ((bl :: caps).map (·.ty)) (bls.map (·.ty) ++ source.toList) written
  let name := s!"$cont{p.line}_{p.col}_{key.hash}" ++ (if p.file.isEmpty then "" else s!"_{p.file}")
  -- (its effects the function's own: its body is that function's code,
  -- and it may call what is asked for only in the next elaboration, a
  -- `$first…` or `$refine…`, whose effects this one cannot see)
  let heap := ["reads", "writes", "allocates"].filter fun k => ctx.fnFx.contains k || fxB.any (·.1 == k)
  let (ret, tup, returnExit) := firstResult p name bls sets source
  -- (the `var`s it sets, copied from parameters named `m$in`, and given back)
  let copies := sets.map fun l => SExpr.decl p l.name (some l.ty.toSTy) true (.ident p s!"{l.name}$in")
  let params : List SParam := { name := b, ty := bl.ty.toSTy } ::
    caps.map fun l => { name := if sets.any (·.name == l.name) then s!"{l.name}$in" else l.name, ty := l.ty.toSTy }
  -- (`$firstP`: the clauses are lifted already, the consumer's, which lifting
  -- again would bind twice, as for #275's functions)
  return { key, pos := p, name, returnExit, sourceContext := sourceContextOf ctx, inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
           params := params ++ typeParams, tparams := tps,
           specs := (if heap.isEmpty then ["computes"] else heap) ++ ["decides"],
           ret,
           body := ctx.choiceCoercionBody (pruneConstructHints ctx name
             (.block p (copies ++ [.app p (.ident p "$firstP") [.block p (rest ++ [tup])] false]))),
           binds, sets := sets.map (·.name),
           args := SExpr.ident p b :: caps.map (fun l => SExpr.ident p l.name) ++ typeArgs,
           varBinds := (bls.filter (·.mutable)).map (·.name) }

/-- The return slot is written by a moved consumer's source return. Its
    self-assignment is metadata for capture/write analysis, not executed. -/
def forReturnBody? : SExpr → Bool
  | .app _ (.ident _ f) _ false => f == "$forReturns" || f == "$forReturnBody"
  | _ => false

/-- Restore source exits for the current filter, while a body's own
    marker restores only its return target at actual body entry. -/
def forClauseExitScope (body inner : SExpr) : SExpr :=
  match body with
  | .app p (.ident _ f) [.block _ [metadata, breaking], mode, _] false =>
    if f == "$forReturns" || f == "$forReturnBody" then
      .app p (.ident p "$forClauseExits") [metadata, breaking, mode, inner] false
    else inner
  | .app p (.ident _ f) [metadata, mode, _] false =>
    if f == "$forReturns" || f == "$forReturnBody" then
      .app p (.ident p "$forReturnBody") [metadata, mode, inner] false
    else inner
  | _ => inner

def forStageBodyAs (body inner : SExpr) : SExpr :=
  match body with
  | .app p f@(.ident _ n) [metadata, mode, _] false =>
    if n == "$forReturns" || n == "$forReturnBody" then .app p f [metadata, mode, inner] false else inner
  | _ => inner

/-- Keep source breaks aimed at their original loop after adding the
    producer's private abort loop. Its own outcome abort is left alone. -/
partial def forwardForBreaks (abort escaped : Nat) : Expr → Expr
  | e@(.loop _) => e
  | e@(.ite (.prim .query [.local j]) yes (.seq .brk (.prim .userErr []))) =>
    if j == abort then e else
      .ite (.prim .query [.local j]) (forwardForBreaks abort escaped yes)
        (forwardForBreaks abort escaped (.seq .brk (.prim .userErr [])))
  | e@(.seq (.assign j (.lit (.logic false))) (.seq .brk (.prim .userErr []))) =>
    if j == abort then e else .seq (.assign escaped (.lit (.logic true))) e
  | .brk => .seq (.assign escaped (.lit (.logic true))) .brk
  | .assign i e => .assign i (forwardForBreaks abort escaped e)
  | .seq a b => .seq (forwardForBreaks abort escaped a) (forwardForBreaks abort escaped b)
  | .prim p es => .prim p (es.map (forwardForBreaks abort escaped))
  | .heap p es => .heap p (es.map (forwardForBreaks abort escaped))
  | .call f es => .call f (es.map (forwardForBreaks abort escaped))
  | .ite c t e => .ite (forwardForBreaks abort escaped c) (forwardForBreaks abort escaped t) (forwardForBreaks abort escaped e)
  | .forE i a f b => .forE i (forwardForBreaks abort escaped a) (forwardForBreaks abort escaped f) (forwardForBreaks abort escaped b)
  | .ret e => .ret (forwardForBreaks abort escaped e)
  | .print e => .print (forwardForBreaks abort escaped e)
  | e => e

/-- Whether a `for` body can move into a continuation. Source returns
    need an explicit outcome; breaks must stay inside the body's loops.
    The enclosing function may suspend; the moved code must remain
    immediate. Discovery also checks typed calls and pending cast lifts. -/
partial def forBodySafe (ctx : Ctx) (body : SExpr) : Bool :=
  let returns := forReturnBody? body
  -- Prepared consumers keep lazy producer templates (including groups and
  -- generic/default argument bindings) inside the body. Their ownership is
  -- checked when that consumer elaborates; they do not escape the helper.
  let safeMarkers := ["$sourceSuper", "$methodMiss", "$methodCast", "$methodCase", "$methodType", "$methodParams", "$inlineScope", "$inlineScopeEnd", "$inline", "$choice", "$excl", "$alt", "$firstP", "$first", "$each", "$noLift", "$fxOf",
    "$forReturns", "$forReturnBody", "$forClauseExits", "$choiceOperation", "$choiceGenericOperation", "$choiceCoercions", "$choiceDictionary", "$defer", "$loop", "$rec", "$recTo", "$group", "$member", "$returnTail",
    "$tparams", "$params", "$defaults", "$paramDefault", "$freeNames", "$declNames", "$callArgs", "$callSingleton"]
  let rec blocked (e : SExpr) : Bool :=
    match e with
    -- Starting a task is immediate. elabSpawn checks its arguments in the
    -- caller and the waiting callee in its own suspension context.
    | .app _ (.ident _ "$spawn") _ false => false
    | e => (match e with
      | .ret .. => !returns
      | .app _ (.ident _ f) _ _ =>
        (f.startsWith "$" && !safeMarkers.contains f) || f == "Sleep" ||
          ((ctx.sig? f).map fun s => s.suspends || s.fx.contains "no_rollback").getD false
      | _ => false) || e.children.any blocked
  !(Refine.findPart (fun | .brk _ => true | _ => false) true body).isSome && !blocked body

/-- A shared for continuation runs inside a filter, so cannot suspend.
    Method/function-value calls need their typed signatures; a cast still
    being discovered can hide its suspension behind a placeholder. -/
def forContWaits (ctx : Ctx) (before after : ESt) (code : List Expr) : Bool :=
  ctx.suspends && (before.pendingSuspendingCasts != after.pendingSuspendingCasts ||
    before.pendingWaitingCasts != after.pendingWaitingCasts ||
    code.any (Suspend.hasSusp fun f => ctx.sigs.any fun s => s.idx == f && s.suspends))

/-- An admitted continuation rediscovers its local/frame metadata in its
    own helper. Its heap effects still belong to the enclosing source. -/
def restoreForContTrial (saved : ESt) : EM Unit := do
  let fx := (← get).fx
  set { saved with fx }

/-- (#335, phase 2) The continuation of a composed choice in a `for`: a
    function that runs the clauses after it (`rest`) and the body, failing
    where their first filter fails (`$forFirst`), and gives the values (and
    the final values of the `var`s they set), called from each alternative's
    own `for`. Its binding's type `bty`, the values' type `vty`. Or why not,
    and the clauses are copied, as before. -/
def contForLiftOf (ctx : Ctx) (p : Pos) (b : String) (bty vty : Ty) (alts rest : List SExpr) (body : SExpr) (outcome : Bool := false) :
    Except String Choice.FirstLift := do
  let ctx := ctx.choiceCoercionScope
  let written := ctx.choiceCoercionBody (.block p (rest ++ [body]))
  let key := (if outcome then "fo" else "f") ++ contKey ctx p b (alts ++ rest ++ [body])
  let σt := ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let rest := rest.map (Refine.substTypes σt)
  let body := Refine.substTypes σt body
  let (rest, body) ← match ctx.selfClass with
    | some c =>
      pure (rest.map (selfQualify ctx c), selfQualify ctx c body)
    | none => pure (rest, body)
  if !forReturnBody? body &&
      (Refine.findPart (fun | .ret .. => true | _ => false) false written).isSome then throw "a return"
  let body := match body with
    | .app q (.ident _ "$forReturns") args false => .app q (.ident q "$forReturnBody") args false
    | b => b
  let breaks := match body with
    | .app _ (.ident _ "$forReturnBody") [.block _ [_, .set _ (.ident _ _) none _], _, _] false => true
    | _ => false
  if !breaks && (Refine.findPart Refine.isBreak true (.block p rest)).isSome then throw "a break"
  let caps : List Local := (Choice.namesUsed (ctx.choiceCoercionBody (.block p (rest ++ [body])))).eraseDups.filterMap ctx.lookup
  let setNames := Choice.setsIn (.block p (rest ++ [body]))
  let sets := caps.filter fun l => l.mutable && setNames.contains l.name
  let (tps, typeParams, typeArgs) ← contTypes ctx p (bty :: caps.map (·.ty)) [vty] written
  let name := s!"$contf{p.line}_{p.col}_{key.hash}" ++ (if p.file.isEmpty then "" else s!"_{p.file}")
  let heap := ["reads", "writes", "allocates"].filter fun k => ctx.fnFx.contains k
  let copies := sets.map fun l => SExpr.decl p l.name (some l.ty.toSTy) true (.ident p s!"{l.name}$in")
  let params : List SParam := { name := b, ty := bty.toSTy } ::
    caps.map fun l => { name := if sets.any (·.name == l.name) then s!"{l.name}$in" else l.name, ty := l.ty.toSTy }
  let vals := s!"{b}$vals"
  let valueTy : STy := if outcome then .opt (.arr vty.toSTy) else .arr vty.toSTy
  let failure : SExpr := if sets.isEmpty then .ident p "false" else
    .tuple p (.ident p "false" :: sets.map fun l => SExpr.ident p l.name)
  let ffirst : SExpr := if outcome then
      .app p (.ident p "$forFirstOutcome") [.block p rest, body, failure] false
    else .app p (.ident p "$forFirst") [.block p rest, body] false
  let ffirst := match body with
    | .app q (.ident _ "$forReturnBody") [.block _ [metadata, breaking], mode, _] false =>
      .app q (.ident q "$forClauseExits") [metadata, breaking, mode, ffirst] false
    | .app q (.ident _ "$forReturnBody") [metadata, mode, _] false =>
      -- Clauses and body leave the same source function. A clause return
      -- succeeds with the packet, committing this filter's copy-outs.
      .app q (.ident q "$forReturnBody") [metadata, mode, ffirst] false
    | _ => ffirst
  let ret : STy := if sets.isEmpty then valueTy else .tup (valueTy :: sets.map (·.ty.toSTy))
  let bodyE : SExpr := if sets.isEmpty then .block p (copies ++ [ffirst]) else
    .block p (copies ++ [.decl p vals none false ffirst, .tuple p (.ident p vals :: sets.map fun l => SExpr.ident p l.name)])
  return { key, pos := p, name, sourceContext := sourceContextOf ctx, inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
           params := params ++ typeParams, tparams := tps,
           specs := (if heap.isEmpty then ["computes"] else heap) ++ ["decides"],
           ret, body := ctx.choiceCoercionBody (pruneConstructHints ctx name bodyE), binds := [], sets := sets.map (·.name),
           args := SExpr.ident p b :: caps.map (fun l => SExpr.ident p l.name) ++ typeArgs }

/-- The resume interface keeps every caller/frame type argument. A result
    alone can erase equations needed by borrowed frame-reference arguments. -/
def forStagePlanOf (ctx : Ctx) (p : Pos) (key : String) (clauses : List SExpr)
    (body : SExpr) (vty : Ty) (outcome : Bool) (required : List String := [])
    (sourceSuspends : Bool := false) : Except String Choice.FirstLift := do
  let ctx := ctx.choiceCoercionScope
  let qualify := match ctx.selfClass with | some c => selfQualify ctx c | none => id
  let clauses := clauses.map qualify
  let body := qualify body
  let written := ctx.choiceCoercionBody (.block p (clauses ++ [body] ++ required.map (SExpr.ident p ·)))
  let used := Choice.namesUsed written
  let caps := used.eraseDups.filterMap ctx.lookup
  let setNames := Choice.setsIn written
  let sets := caps.filter fun l => l.mutable && setNames.contains l.name
  let inputs := (caps.flatMap fun l => l.storage.toList.flatMap (·.args)) ++ ctx.choiceCoercions.map (·.1.ty)
  let (tps, _, _) ← contTypes ctx p inputs (vty :: sets.map (·.ty)) (.tuple p [])
  let base := s!"$forStage{p.line}_{p.col}_{key.hash}"
  let method := base ++ "$resume"
  let specs := (if ctx.fnFx.isEmpty then ["computes"] else ctx.fnFx) ++ ["suspends"]
  let copies := sets.map fun l => (l.name, l.ty.toSTy)
  let borrowed := caps.filterMap fun l => if l.storage.isSome then some l.name else none
  let plan : Choice.ForStagePlan := {
    key, pos := p, base, method, tparams := tps,
    value := vty.toSTy, copies, borrowed, specs, outcome, sourceSuspends }
  let valueTy := if outcome then STy.opt (.arr plan.value) else .arr plan.value
  let ret := if copies.isEmpty then valueTy else .tup (valueTy :: copies.map (·.2))
  let cls := STop.classDef p base tps [] [] true [] []
    [.fn p method [] [] ("$abstract" :: specs) ret (.tuple p [])]
  return {
    stageOnly := true, stagePlan := some plan, key, pos := p, name := base,
    params := [], specs := ["computes"], ret := .name "void", body := .tuple p [],
    binds := [], sets := [], args := [], extraFns := [cls] }

/-- Storage and the ordered root view are part of generated-code identity. -/
def forStageCaptureKey (ctx : Ctx) (args : List Ty) (caps : List Local) : String :=
  let origins := caps.map fun l => s!"{l.name}:{l.mutable}:" ++ match l.storage with
    | none => "local"
    | some s => s!"{s.frame}:{s.name}:{reprStr s.args}"
  s!"{ctx.frameName}:{ctx.refineScope}:{ctx.inChoice}:{ctx.inRepeat}:" ++
    reprStr args ++ String.intercalate ";" origins

def forStageView (base : String) (args : List STy) : STy :=
  if args.isEmpty then .name base else .app base args

def forStageCopyMetadata (p : Pos) (names : List String) : SExpr :=
  .block p (names.map fun n => .set p (.ident p n) none (.ident p n))

def forStageCopyNames (ids : List SExpr) : List String :=
  ids.filterMap fun
    | .set _ (.ident _ n) none _ => some n
    | .ident _ n => some n
    | _ => none

/-- A shared prefix still runs in the alternative's current filter. Its
    singleton environment is resumed only from that alternative's body. -/
def forStageInvoke (p : Pos) (prepare : Choice.FirstLift) (borrowed : List String)
    (body : SExpr) : List SExpr × SExpr :=
  let payload := prepare.name ++ "$ready"
  let packet := payload ++ "$packet"
  let call := SExpr.app p (.ident p prepare.name) prepare.args true
  let get (j : Nat) := SExpr.app p (.ident p packet) [.int p (j : Int)] false
  let clauses := if prepare.sets.isEmpty then [.decl p payload none false call] else
    .decl p packet none false call ::
      (prepare.sets.zipIdx.map fun (n, j) => .set p (.ident p n) none
        (.app p (.ident p "$refineCopyOut") [get (j + 1)] false)) ++
      [.decl p payload none false (get 0)]
  let resume := SExpr.app p (.ident p "$forResumeValues")
    [.ident p payload, forStageCopyMetadata p prepare.sets,
      .block p (borrowed.map (SExpr.ident p ·))] false
  (clauses, forStageBodyAs body resume)

/-- Give the immediate prefix an actual function boundary. A source exit
    returns its normal packet even from nested source loops; ordinary prefix
    failure still fails the call in the caller's original filter. -/
def forStagePrefixOf (ctx : Ctx) (plan : Choice.ForStagePlan) (args : List Ty) (p : Pos)
    (clauses : List SExpr) (body : SExpr) (flat : Bool := false)
    (copyNames : List String := plan.copies.map (·.1))
    (borrowNames : List String := plan.borrowed) : Except String Choice.FirstLift := do
  let ctx := ctx.choiceCoercionScope
  let qualify := match ctx.selfClass with | some c => selfQualify ctx c | none => id
  -- Default annotations use private lexical aliases. Resolve them before
  -- the prefix moves into a function with only its own type parameters.
  let σt := ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let clauses := clauses.map fun e => Refine.substTypes σt (qualify e)
  let body := Refine.substTypes σt (qualify body)
  let written := ctx.choiceCoercionBody (.block p (clauses ++ [body] ++ (copyNames ++ borrowNames).map (SExpr.ident p ·)))
  let caps := (Choice.namesUsed written).eraseDups.filterMap ctx.lookup
  let key := s!"prefix{flat}" ++ plan.key ++ contKey ctx p "$prepare" [written] ++ forStageCaptureKey ctx args caps
  let name := s!"{plan.base}$prepare{key.hash}"
  let (tps, more, witnesses) ← contTypes ctx p (caps.map (·.ty)) args written
  let params := caps.map fun l => ({ name := if l.mutable then l.name ++ "$in" else l.name, ty := l.ty.toSTy } : SParam)
  let init := caps.filterMap fun l => if !l.mutable then none else some
    (SExpr.decl p l.name (some l.ty.toSTy) true
      (.app p (.ident p "$refineCopyIn") [.ident p (l.name ++ "$in")] false))
  let view := forStageView plan.base (args.map Ty.toSTy)
  let stage := SExpr.app p (.ident p "$forStage")
    [.str p [.text plan.base], .decl p "$stageView" (some view) false (.tuple p []),
      forStageCopyMetadata p copyNames, .block p (borrowNames.map (SExpr.ident p ·)),
      .ident p "true", .ident p (if flat then "true" else "false"), .block p clauses, body] false
  let stage := forClauseExitScope body stage
  let value := s!"{name}$value"
  let code := if plan.copies.isEmpty then stage else SExpr.block p
    [.decl p value none false stage, .tuple p (.ident p value :: copyNames.map (SExpr.ident p ·))]
  let valueTy := if plan.outcome then STy.opt (.arr view) else .arr view
  let σ := (plan.tparams.map (·.name)).zip (args.map Ty.toSTy)
  let ret := if plan.copies.isEmpty then valueTy else .tup (valueTy :: plan.copies.map (fun (_, t) => t.substNames σ))
  let storage := caps.filterMap fun l => l.storage.map fun s =>
    (if l.mutable then l.name ++ "$in" else l.name,
      ({ frame := s.frame, name := s.name, args := s.args.map Ty.toSTy } : Choice.ResumeStorage))
  let info : Choice.ForResume := {
    name, storage, inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag,
    inRepeat := ctx.inRepeat, inChoice := ctx.inChoice, sourceContext := sourceContextOf ctx }
  return {
    key, pos := p, name, params := params ++ more, tparams := tps,
    specs := plan.specs.filter (· != "suspends") ++ ["decides"], ret,
    body := ctx.choiceCoercionBody (pruneConstructHints ctx name (.block p (init ++ [code]))),
    binds := [], sets := copyNames,
    args := caps.map (fun l => .ident p l.name) ++ witnesses.map (fun
      | .app q (.ident _ "$witness") [.ident _ n] false =>
        .app q (.ident q "$stageWitness") [.decl q n (some (.name n)) false (.tuple q [])] false
      | e => e), resumes := [info] }

/-- Close over the remaining generators/body without executing either.
    A class retains existential bindings and supplies a typed resume method;
    mutable local aliases still name their original source-frame storage. -/
def forStageEnvOf (ctx : Ctx) (plan : Choice.ForStagePlan) (p : Pos)
    (clauses : List SExpr) (body : SExpr) : Except String (Choice.FirstLift × SExpr × Ty) := do
  let ctx := ctx.choiceCoercionScope
  let qualify := match ctx.selfClass with | some c => selfQualify ctx c | none => id
  let clauses := clauses.map qualify
  let body := qualify body
  let written := ctx.choiceCoercionBody (.block p (clauses ++ [body] ++ (ctx.forStageCopies ++ ctx.forStageBorrows).map (SExpr.ident p ·)))
  let caps := (Choice.namesUsed written).eraseDups.filterMap ctx.lookup
  let key := s!"env{ctx.forStageFlat}" ++ plan.key ++ contKey ctx p "$resume" [written] ++ forStageCaptureKey ctx ctx.forStageArgs caps
  let name := s!"{plan.base}$env{key.hash}"
  let args := ctx.forStageArgs
  let (tps, _, _) ← contTypes ctx p (args ++ caps.map (·.ty) ++
    caps.flatMap (fun l => l.storage.toList.flatMap (·.args))) [] written
  let σ := (plan.tparams.map (·.name)).zip (args.map Ty.toSTy) ++
    ctx.types.tvars.map fun (n, t) => (n, t.toSTy)
  let rename := Choice.renameE [("Self", "$sourceSelf")]
  let clauses := clauses.map fun e => rename (Refine.substTypes σ e)
  let body := rename (Refine.substTypes σ body)
  let body := match body with
    | .app p (.ident _ "$forReturns") args false => .app p (.ident p "$forReturnBody") args false
    | b => b
  let localName (n : String) := if n == "Self" then "$sourceSelf" else n
  let fields := caps.zipIdx.map fun (l, j) => (s!"$capture{j}", l.ty.toSTy, none, false)
  let borrowed (l : Local) := l.storage.filter fun s =>
    !(ctx.sig? s.frame).any (!·.suspends)
  let init := caps.zipIdx.flatMap fun (l, j) =>
    let value := SExpr.app p (.ident p "$forEnvCapture")
      [.member p (.ident p "Self") s!"$capture{j}"] false
    if (borrowed l).isSome then
      let saved := s!"$captureInit{j}"
      [SExpr.decl p saved (some l.ty.toSTy) false value,
        .decl p (localName l.name) (some l.ty.toSTy) l.mutable
          (.app p (.ident p "$forEnvInit") [.ident p saved] false)]
    else [SExpr.decl p (localName l.name) (some l.ty.toSTy) l.mutable value]
  let copies := ctx.forStageCopies.map fun n => SExpr.ident p (localName n)
  let vals := s!"{name}$values"
  let failed : SExpr := if copies.isEmpty then .ident p "false" else .tuple p (.ident p "false" :: copies)
  let run := if plan.outcome then
      SExpr.app p (.ident p "$forFirstOutcome") [.block p clauses, body, failed] false
    else SExpr.app p (.ident p "$forFirst") [.block p clauses, body] false
  let run := forClauseExitScope body run
  let run := if ctx.forStageFlat then SExpr.app p (.ident p "$forStageFlatten") [run] false else run
  let code := if copies.isEmpty then run else .block p
    [.decl p vals none false run, .tuple p (.ident p vals :: copies)]
  let valueTy := if plan.outcome then STy.opt (.arr (plan.value.substNames σ)) else .arr (plan.value.substNames σ)
  let ret := if copies.isEmpty then valueTy else
    .tup (valueTy :: plan.copies.map (fun (_, t) => t.substNames σ))
  let method := STop.fn p plan.method [] [] ("override" :: plan.specs) ret
    (pruneConstructHints ctx s!"{name}.{plan.method}" (.block p (init ++ [ctx.choiceCoercionBody code])))
  let storage := caps.filterMap fun l => (borrowed l).map fun s =>
    (localName l.name, ({ frame := s.frame, name := s.name, args := s.args.map Ty.toSTy } : Choice.ResumeStorage))
  let resumeInfo : Choice.ForResume := {
    name := s!"{name}.{plan.method}", storage,
    inlineScopes := ctx.inlineScopes, liftTag := ctx.liftTag, sourceContext := sourceContextOf ctx }
  let cls := STop.classDef p name tps [] [forStageView plan.base (args.map Ty.toSTy)] false fields [] [method]
  let req : Choice.FirstLift := {
    stageOnly := true, resumes := [resumeInfo], key, pos := p, name,
    params := [], specs := ["computes"], ret := .name "void", body := .tuple p [],
    binds := [], sets := [], args := [], extraFns := [cls] }
  let obj := SExpr.construct p name (tps.map fun tp => .name tp.name)
    (caps.zipIdx.map fun (l, j) => .decl p s!"$capture{j}" none false (.ident p l.name))
  return (req, obj, .struct plan.base args)

/-- A failed body is unwrapped in an iteration body. Inside an outcome
    producer, stop its private loop instead of failing the filter. -/
def forOutcomeValues (ctx : Ctx) (p : Pos) (r : R) : EM R := do
  let .opt (.arr t) := r.ty | eerr p "internal: expected a for outcome"
  -- A waiting method returns before its outcome can be queried. Only the
  -- saved option belongs in a condition; the call stays outside it.
  let (before, input) ← if ctx.suspends && Suspend.hasSusp
      (fun f => ctx.sigs.any fun s => s.idx == f && s.suspends) r.e then do
      let slot ← fresh r.ty
      pure ([Expr.assign slot r.e], Expr.local slot)
    else pure ([], r.e)
  let value := Expr.prim .query [input]
  if let some flag := ctx.forOutcomeSlot then
    let slot ← fresh (.arr t)
    return ⟨before.foldr Expr.seq (.ite (.assign slot value) (.local slot)
      (.seq (.assign flag (.lit (.logic false))) (.seq .brk (.prim .userErr [])))), .arr t⟩
  return ⟨before.foldr Expr.seq value, .arr t⟩

/-- Operation dictionaries retain the selected value's precise type. The
    generated adapters are instantiated before calling the shared suffix. -/
structure ChoiceOperations where
  plan : ChoiceTypes.Plan
  bindingName : String := ""
  params : List (String × Ty) := []
  replacements : List (SExpr × SExpr) := []
  knownTypes : List (SExpr × Ty) := []
  coercions : List (String × Ty × Ty) := []
  casePrelude : List (List SExpr) := []
  extraFns : List STop := []

partial def ChoiceOperations.rewrite (ops : ChoiceOperations) (body : SExpr) : SExpr :=
  if ops.replacements.isEmpty then body else
  Choice.mapE (fun
    -- Getters are values, not assignment targets. Retain the source path
    -- for the complete lvalue; discovery falls back if it needs its layout.
    | call@(.set p target op value) =>
      some <| ((ops.replacements.find? (·.1 == call)).map (·.2)).getD
        (.set p target op (ops.rewrite value))
    | call@(.app _ (.member ..) _ _) | call@(.member ..) =>
      (ops.replacements.find? (·.1 == call)).map (·.2)
    | _ => none) body

def ChoiceOperations.context (ops : ChoiceOperations) (ctx : Ctx) : EM Ctx := do
  let mut ctx := ctx
  for (name, ty) in ops.params do
    let slot ← fresh ty
    ctx := { ctx with locals := { name, slot, ty, mutable := false } :: ctx.locals }
  return ctx

def ChoiceOperations.lift (ops : ChoiceOperations) (key : String) (lift : Choice.FirstLift) : Choice.FirstLift :=
  { lift with key, casePrelude := ops.casePrelude, extraFns := lift.extraFns ++ ops.extraFns }

/-- Checked conversion evidence for a numeric choice column. The source
    is still elaborated with that column as its expected type. -/
def choiceNumericConversions (ctx : Ctx) (stem : String) (ops0 : ChoiceOperations) : ChoiceOperations := Id.run do
  let mut ops := ops0
  let p : Pos := { line := 0, col := 0 }
  for (typeName, bound) in ops.plan.params do
    let target := Ty.param typeName bound
    if ops.coercions.any (·.2.2 == target) then continue
    let actuals := ops.plan.instances.map fun row => (target.subst row).subst ctx.types.tvars
    if !actuals.all (fun ty => ty == .int || ty == .rational) || !actuals.contains .rational then continue
    let family := s!"$choiceOperationDictionary{(reprStr ("convertInt", actuals)).hash}"
    let name := s!"{stem}$convert{ops.coercions.length}"
    let variables := ["$convertSource", "$convertTarget"]
    let tps : List TParam := variables.map fun n => { pos := p, name := n, constraint := "type" }
    let familyTy := STy.app family (variables.map STy.name)
    let iface := STop.classDef p family tps [] [] true [] []
      [.fn p "$apply" [{ name := "$value", ty := .name "$convertSource" }] []
        ["$abstract", "computes"] (.name "$convertTarget") (.tuple p [])]
    let applyFn := STop.fn p (family ++ "$apply")
      [{ name := "$Self", ty := familyTy }, { name := "$value", ty := .name "$convertSource" }]
      tps ["computes"] (.name "$convertTarget")
      (.app p (.member p (.ident p "$Self") "$apply") [.ident p "$value"] false)
    let mut definitions := [iface, applyFn]
    let mut bindings : List (List SExpr) := []
    for (actual, i) in actuals.zipIdx do
      let impl := s!"{family}$case{i}"
      let instanceTy := STy.app family [Ty.int.toSTy, actual.toSTy]
      definitions := definitions ++ [STop.classDef p impl [] [] [instanceTy] false [] []
        [.fn p "$apply" [{ name := "$value", ty := Ty.int.toSTy }] [] ["override", "computes"]
          actual.toSTy (.ident p "$value")]]
      bindings := bindings ++ [[SExpr.decl p name (some instanceTy) false
        (.app p (.ident p "$choiceDictionary") [.construct p impl [] []] false)]]
    ops := { ops with
      params := ops.params ++ [(name, .struct family [.int, target])],
      coercions := ops.coercions ++ [(name, .int, target)],
      casePrelude := (ops.casePrelude.zip bindings).map fun (old, next) => old ++ next,
      extraFns := ops.extraFns ++ definitions }
  return ops

def ChoiceOperations.coercionContext (ops : ChoiceOperations) (body : SExpr) : SExpr :=
  if ops.coercions.isEmpty then body else
  let p := body.pos
  let metadata := ops.coercions.map fun (name, source, target) => SExpr.tuple p
    [.ident p name, .construct p "$choiceConversion" [source.toSTy, target.toSTy] []]
  .app p (.ident p "$choiceCoercions") [.block p metadata, body] false

/-- The selected binding and immutable aliases, in reverse lexical order.
    An alias retains its initializer so its checked result can be recovered
    after the initializer's operations have been discovered. -/
abbrev ChoiceAliases := List (String × Option SExpr)

def ChoiceOperations.aliasTypes (ops : ChoiceOperations) (bindings : ChoiceAliases) : List (String × Ty) := Id.run do
  let mut types : List (String × Ty) := []
  for (name, source) in bindings.reverse do
    let ty := match source with
      | none => some ops.plan.binding
      | some (.ident _ original) => types.lookup original
      | some value => (ops.knownTypes.find? (·.1 == value)).map (·.2)
    if let some ty := ty then types := (name, ty) :: types
  return types

/-- A source assignment may follow fields from a local, but not write
    through a call result. Index paths have a separate evaluation order. -/
def choiceFieldPath : SExpr → Bool
  | .ident .. => true
  | .member _ receiver _ => choiceFieldPath receiver
  | _ => false

/- Discover operations in lexical order, retaining immutable aliases only
    where their declarations are in scope. The source aliases remain intact:
    dictionary discovery needs their types, not a substitution of their values. -/
mutual
partial def choiceMemberOperations (bindings : ChoiceAliases) (body : SExpr) : List (SExpr × ChoiceAliases) :=
  let names := bindings.map (·.1)
  let depends (receiver : SExpr) := (Choice.namesUsed receiver).any names.contains
  match body with
  | e@(.app _ member@(.member _ receiver _) arguments _) =>
    choiceMemberOperations bindings receiver ++ arguments.flatMap (choiceMemberOperations bindings) ++
      (if depends receiver then [(member, bindings), (e, bindings)] else [])
  | e@(.member _ receiver _) =>
    choiceMemberOperations bindings receiver ++ (if depends receiver then [(e, bindings)] else [])
  | .block _ statements => (choiceMemberOperationSeq bindings statements).1
  | .forE _ clauses body =>
    let (operations, visible) := choiceMemberOperationSeq bindings clauses
    operations ++ choiceMemberOperations visible body
  | .ite _ conditions yes no =>
    let (operations, visible) := choiceMemberOperationSeq bindings conditions
    operations ++ choiceMemberOperations visible yes ++ no.toList.flatMap (choiceMemberOperations bindings)
  | e@(.set _ target@(.app _ (.member _ receiver _) [index] true) op value) =>
    let old := match value with
      | .app _ (.ident _ "$withOld") [saved, _] false => saved
      | _ => target
    choiceMemberOperations bindings index ++ choiceMemberOperations bindings receiver ++
      (if op.isSome then choiceMemberOperations bindings old else []) ++
      choiceMemberOperations bindings value ++ (if depends receiver then [(e, bindings)] else [])
  | e@(.set _ target@(.member _ receiver _) op value) =>
    let old := match value with
      | .app _ (.ident _ "$withOld") [saved, _] false => saved
      | _ => target
    choiceMemberOperations bindings receiver ++
      (if op.isSome then choiceMemberOperations bindings old else []) ++
      choiceMemberOperations bindings value ++ (if depends receiver then [(e, bindings)] else [])
  | .set _ _ _ value => choiceMemberOperations bindings value
  | .structDef .. | .enumDef .. | .refineDef .. => []
  | .app _ (.ident _ "$constructHints") _ _ => []
  | e => e.children.flatMap (choiceMemberOperations bindings)

partial def choiceMemberOperationSeq (bindings : ChoiceAliases) (statements : List SExpr) :
    List (SExpr × ChoiceAliases) × ChoiceAliases := Id.run do
  let mut visible := bindings
  let mut operations := []
  for statement in statements do
    operations := operations ++ choiceMemberOperations visible statement
    if let .decl _ name none false value := statement then
      let candidate := match value with
        | .ident .. | .member .. | .app _ (.member ..) _ _ => true
        | _ => false
      if candidate && (Choice.namesUsed value).any (fun n => visible.any (·.1 == n)) then
        visible := (name, some value) :: visible
  return (operations, visible)
end

/-- A concrete operation contract before abstracting its type columns. -/
structure ChoiceOperationCase where
  receiver : Ty
  inputs : List Ty
  result : Ty
  specs : List String
  methodVars : List (String × Bool) := []
  omittedDefaults : Bool := false
  indexedDecides : Bool := true

def choiceOrderedArguments (args : List SExpr) : List SExpr :=
  let named : SExpr → Bool := fun | .decl _ n .. => n.startsWith "?" | _ => false
  args.filter (!named ·) ++ args.filter named

def choiceArgumentValue : SExpr → SExpr
  | arg@(.decl _ n _ _ value) => if n.startsWith "?" then value else arg
  | value => value

def choiceForwardArguments (written values : List SExpr) : List SExpr :=
  (written.zip values).map fun (arg, value) => match arg with
    | .decl p n _ _ _ => if n.startsWith "?" then .decl p n none false value else value
    | _ => value

/-- Parameter types in evaluation order. Omitted defaults stay in the
    original method call, in its own declaration and type scope. -/
def choiceCallInputs (sig : Sig) (args : List SExpr) : Option (List Ty × Bool) := do
  let npos := sig.params.length - sig.named.length - 1
  let positional := args.filter fun | .decl _ n .. => !n.startsWith "?" | _ => true
  let named := args.filterMap fun | .decl _ n .. => if n.startsWith "?" then some (n.drop 1).toString else none | _ => none
  if positional.length != npos || named.eraseDups.length != named.length then none else do
  let indices ← named.mapM fun n => (sig.named.findIdx? (·.1 == n)).map (npos + ·)
  let omitted := sig.named.filter fun (n, _) => !named.contains n
  if omitted.any (·.2.isNone) then none else
    some ((List.range npos ++ indices).map fun i => sig.params[i + 1]!, !omitted.isEmpty)

def choiceDefaultContext (ctx : Ctx) (body : SExpr) : SExpr :=
  let p := body.pos
  let flags : Nat := (if ctx.inRepeat then 1 else 0) + (if ctx.inDefer then 2 else 0) + (if ctx.inDefaultCheck then 4 else 0)
  let stack := ctx.defaults.map fun (f, n) => SExpr.tuple p [.str p [.text f], .str p [.text n]]
  .app p (.ident p "$defaultContext") [.block p stack, .int p (flags : Int), body] false

/-- Defaults are checked where the source call occurs, including a loop
    or deferred body nested in the shared suffix. -/
partial def choiceOperationContexts (ctx : Ctx) (body : SExpr) : List (SExpr × Ctx) :=
  let here := match body with | .app _ (.member ..) _ _ => [(body, ctx)] | _ => []
  here ++ (match body with
    | .forE _ clauses value => clauses.flatMap (choiceOperationContexts ctx) ++
        choiceOperationContexts { ctx with inRepeat := true } value
    | .loop _ value => choiceOperationContexts { ctx with inRepeat := true } value
    | .app _ (.ident _ "$defer") values _ => values.flatMap (choiceOperationContexts { ctx with inDefer := true })
    | .app _ (.ident _ "$defaultContext") [.block _ stack, .int _ flags, value] false =>
        let defaults := stack.filterMap fun
          | .tuple _ [.str _ [.text f], .str _ [.text n]] => some (f, n)
          | _ => none
        choiceOperationContexts { ctx with
          defaults := defaults ++ ctx.defaults,
          inRepeat := flags % 2 == 1, inDefer := flags / 2 % 2 == 1,
          inDefaultCheck := flags / 4 % 2 == 1 } value
    | .structDef .. | .enumDef .. | .refineDef .. => []
    | _ => body.children.flatMap (choiceOperationContexts ctx))

/-- A generic dictionary quantifies method parameters at the call, after
    later generators have supplied their values. Only receiver-dependent
    columns independent of those method parameters belong to its object. -/
def choiceGenericOperation (ctx : Ctx) (stem : String) (receiver : SExpr) (receiverTy : Ty) (ops : ChoiceOperations)
    (call : SExpr) (cases : List ChoiceOperationCase) : Option ChoiceOperations := do
  let .app p (.member _ _ method) arguments bracket := call | none
  let arguments := choiceOrderedArguments arguments
  let borrows := cases.any (·.omittedDefaults)
  let count := (cases.head?.map (·.methodVars.length)).getD 0
  if count == 0 || cases.any (·.methodVars.length != count) then none else do
  let methodVars := (List.range count).map fun i =>
    (s!"$operationMethod{i}", cases.any fun row => (row.methodVars[i]!).2)
  let methodTypes := methodVars.map fun (n, b) => (n, Ty.param n b)
  let methodNames := methodVars.map (·.1)
  let cases := cases.map fun (row : ChoiceOperationCase) => { row with
    inputs := row.inputs.map (Ty.subst methodTypes), result := row.result.subst methodTypes }
  let mut extended := ops.plan
  let mut inputs : List Ty := []
  for j in List.range arguments.length do
    let (next, input) := ChoiceTypes.extend ctx.types stem extended (cases.map fun row => row.inputs[j]!)
    extended := next
    inputs := inputs ++ [input]
  let (extendedPlan, result) := ChoiceTypes.extend ctx.types stem extended (cases.map (·.result))
  -- An associated type containing a method parameter cannot be fixed
  -- before that method is invoked. Such a type needs a richer schema.
  if extendedPlan.instances.any (fun row => row.any fun (_, ty) => ty.params.any methodNames.contains) then none else do
  let signature := receiverTy :: inputs ++ [result]
  let classVars := Ty.mergeParamBounds (signature.flatMap Ty.paramsC) |>.filter (!methodNames.contains ·.1)
  let p0 : Pos := { line := 0, col := 0 }
  let specs := (if cases.any (·.specs.contains "suspends") then ["suspends"] else []) ++
    (if bracket then ["decides"] else []) ++
    (let effects := heapFx.filter fun k => cases.any fun row => (allowedFx row.specs).contains k
     if effects.isEmpty then ["computes"] else effects)
  let canonical := cases.map fun row =>
    let types := row.receiver :: row.inputs ++ [row.result]
    let vars := Ty.mergeParamBounds (types.flatMap Ty.paramsC) |>.filter (!methodNames.contains ·.1)
    let rename := vars.zipIdx.map fun ((n, b), i) => (n, Ty.param s!"$operationT{i}" b)
    (types.map (·.subst rename), vars, rename)
  let context := if borrows then reprStr (choiceDefaultContext ctx (.tuple p [])) else ""
  let labels := arguments.map fun | .decl _ n .. => n | _ => ""
  let familyKey := if !borrows && labels.all (· == "") then reprStr (method, specs, methodVars, canonical.map (·.1)) else
    reprStr (method, specs, methodVars, canonical.map (·.1), labels, context)
  let family := s!"$choiceOperationDictionary{familyKey.hash}{if borrows then "$choiceDefault" else ""}"
  let classNames := classVars.zipIdx.map fun ((_, b), i) => (s!"$operationClass{i}", b)
  let classRename := classVars.zip classNames |>.map fun ((old, _), (name, bound)) => (old, Ty.param name bound)
  let declarationSignature := signature.map (·.subst classRename)
  let classArgs := classNames.map fun (n, _) => STy.name n
  let tparams (vars : List (String × Bool)) : List TParam := vars.map fun (name, bound) =>
    { pos := p0, name, constraint := if bound then "comparable" else "type" }
  let params (types : List Ty) : List SParam := types.zipIdx.map fun (ty, i) => { name := s!"$input{i}", ty := ty.toSTy }
  let values := (List.range (arguments.length + 1)).map fun i => SExpr.ident p0 s!"$input{i}"
  let methodTps := tparams methodVars
  let iface := STop.classDef p0 family (tparams classNames) [] [] true [] []
    [.fn p0 "$apply" (params declarationSignature.dropLast) methodTps ("$abstract" :: specs)
      declarationSignature.getLast!.toSTy (.tuple p0 [])]
  let applyFn := STop.fn p0 (family ++ "$apply")
    ({ name := "$Self", ty := .app family classArgs } :: params declarationSignature.dropLast)
    (tparams classNames ++ methodTps) specs declarationSignature.getLast!.toSTy
    (.app p0 (.member p0 (.ident p0 "$Self") "$apply") values bracket)
  let mut definitions : List STop := [iface, applyFn]
  let mut bindings : List (List SExpr) := []
  for (((row, (_, vars, rename)), instanceTypes), i) in (cases.zip canonical |>.zip extendedPlan.instances).zipIdx do
    let impl := s!"{family}$case{i}"
    let actualClassArgs := classVars.map fun (name, bound) => (Ty.param name bound).subst instanceTypes
    let parentTy := STy.app family (actualClassArgs.map fun t => (Ty.subst rename t).toSTy)
    let implementationTypes := (row.receiver :: row.inputs ++ [row.result]).map (Ty.subst rename)
    let canonicalVars := vars.zipIdx.map fun ((_, b), j) => (s!"$operationT{j}", b)
    let body := SExpr.app p0 (.member p0 values.head! method) (choiceForwardArguments arguments values.tail) bracket
    let body := if borrows then choiceDefaultContext ctx body else body
    definitions := definitions ++ [STop.classDef p0 impl (tparams canonicalVars) [] [parentTy] false [] []
      [.fn p0 "$apply" (params implementationTypes.dropLast) methodTps ("override" :: specs)
        implementationTypes.getLast!.toSTy body]]
    let value := SExpr.construct p impl (vars.map fun (n, _) => .name n) []
    bindings := bindings ++ [[SExpr.decl p s!"{stem}$op{ops.params.length}" (some (.app family (actualClassArgs.map Ty.toSTy))) false
      (.app p (.ident p "$choiceDictionary") [value] false)]]
  let name := s!"{stem}$op{ops.params.length}"
  let methodMetadata := methodVars.map fun (n, b) => SExpr.tuple p [.str p [.text n], .int p (if b then 1 else 0)]
  let instances := extendedPlan.instances.map fun row => SExpr.block p (extendedPlan.params.map fun (n, b) =>
    SExpr.tuple p [.construct p "$choiceVariable" [(Ty.param n b).toSTy] [],
      .construct p "$choiceInstance" [((row.lookup n).getD (.param n b)).toSTy] []])
  let invocation := SExpr.app p (.ident p "$choiceGenericOperation")
    (.str p [.text (FnValues.shapeOf (arguments.length + 1) specs).name] :: .ident p name ::
      .block p methodMetadata :: .construct p "$choiceSignature" (signature.map Ty.toSTy) [] ::
      .block p instances :: ops.rewrite receiver :: arguments.map (ops.rewrite ∘ choiceArgumentValue)) bracket
  some { ops with
    plan := extendedPlan,
    params := ops.params ++ [(name, .struct family (classVars.map fun (n, b) => .param n b))],
    replacements := ops.replacements ++ [(call, invocation)],
    knownTypes := ops.knownTypes ++ (if result.params.any methodNames.contains then [] else [(call, result)]),
    casePrelude := (ops.casePrelude.zip bindings).map fun (old, next) => old ++ next,
    extraFns := ops.extraFns ++ definitions }

/-- Each dictionary implements the method at its original receiver and
    argument types. Omitted defaults retain their declaration scope and
    source context; their forwarding methods borrow caller task ownership. -/
def choiceOperations (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx)
    (stem binding : String) (plan : ChoiceTypes.Plan) (suffix : List SExpr)
    (forBody : Option SExpr := none) : EM ChoiceOperations := do
  let mut ops : ChoiceOperations := { plan, bindingName := binding, casePrelude := plan.instances.map fun _ => [] }
  if !(match plan.binding with | .param .. => true | _ => false) then return ops
  let source : List SExpr := match forBody with
    | some value => suffix.dropLast ++ [.forE value.pos [] value]
    | none => suffix
  let contexts := source.flatMap (choiceOperationContexts ctx)
  let mut seen : List SExpr := []
  for (call, bindings) in (choiceMemberOperationSeq [(binding, none)] suffix).1 do
    let key := call
    if seen.contains key then continue
    seen := key :: seen
    let sourceCtx := (contexts.find? (·.1 == call)).map (·.2) |>.getD ctx
    let indexed := match call with
      | .set _ (.app _ (.member ..) [_] true) _ _ => true
      | _ => false
    let details : Option (Pos × SExpr × String × List SExpr × Bool × Bool × Option (Option String)) := match call with
      | .app p (.member _ receiver method) arguments bracket => some (p, receiver, method, arguments, bracket, false, none)
      | .member p receiver field => some (p, receiver, field, [], false, true, none)
      | .set p target@(.app _ (.member _ receiver field) [index] true) op value =>
        if !choiceFieldPath receiver then none else
        let arguments := match op, value with
          | none, _ => [index, value]
          | some _, .app _ (.ident _ "$withOld") [saved, rhs] false => [index, saved, rhs]
          | some _, _ => [index, target, value]
        some (p, receiver, field, arguments, true, false, some op)
      | .set p target@(.member _ receiver field) op value =>
        if !choiceFieldPath receiver then none else
        let arguments := match op, value with
          | none, _ => [value]
          | some _, .app _ (.ident _ "$withOld") [saved, rhs] false => [saved, rhs]
          | some _, _ => [target, value]
        some (p, receiver, field, arguments, false, false, some op)
      | _ => none
    let some (p, receiver, method, arguments, bracket, isField, setter) := details | continue
    let arguments := choiceOrderedArguments arguments
    let callee := match call with | .app _ fn _ _ => fn | _ => call
    let functionType := if isField then none else (ops.knownTypes.find? (·.1 == callee)).map (·.2)
    let callable := functionType.any fun | .param .. => true | _ => false
    if callable && arguments.any (fun | .decl _ n .. => n.startsWith "?" | _ => false) then continue
    -- Preserve callee-before-argument evaluation, including a mutable
    -- callback replaced by one of its argument expressions.
    let receiver := if callable then callee else receiver
    let aliases := ops.aliasTypes bindings
    let direct := match receiver with | .ident _ n => aliases.lookup n | _ => none
    let known := (ops.knownTypes.find? (·.1 == receiver)).map (·.2)
    let receiverTy ← if direct.isSome then pure direct else if known.isSome then pure known else do
      let saved ← get
      let result ← tryCatch (do
        let probeCtx ← ops.context (← choiceTypeContext ctx ops.plan)
        let mut probeCtx := { probeCtx with typeOnly := true }
        for (name, ty) in aliases do
          let slot ← fresh ty
          probeCtx := { probeCtx with
            locals := { name, ty, slot, mutable := false } :: probeCtx.locals }
        return some (← elabE probeCtx (ops.rewrite receiver) none).ty) (fun _ => pure none)
      set saved
      pure result
    let some receiverTy := receiverTy | continue
    if !(match receiverTy with | .param .. => true | .struct .. => setter.isSome | _ => false) then continue
    let mut cases : List ChoiceOperationCase := []
    for instanceTypes in ops.plan.instances do
      let actual := (receiverTy.subst instanceTypes).subst ctx.types.tvars
      if callable then
        let .struct name types := actual | break
        let some (arity, specs) := FnValues.parseName name | break
        if arity != arguments.length || types.length != arity + 1 || specs.contains "decides" != bracket then break
        cases := cases ++ [{ receiver := actual, inputs := types.dropLast, result := types.getLast!, specs }]
      else if let some op := setter then
        let .struct cls classArgs := actual | break
        if !ctx.types.isRefClass cls || !ctx.types.isVarField cls method then break
        let some (_, fieldTy, _) := (ctx.types.fields cls classArgs).find? (·.1 == method) | break
        if indexed then
          let some (keyTy, leaf, indexedDecides) := (match fieldTy with
            | .arr leaf => some (Ty.int, leaf, true)
            | .map keyTy leaf => some (keyTy, leaf, op.isSome)
            | _ => none) | break
          -- Source paths evaluate keys before capturing their object.
          -- The adapter then reads the current array after the caller RHS.
          cases := cases ++ [{
            receiver := keyTy, inputs := if op.isSome then [actual, leaf, leaf] else [actual, leaf],
            result := leaf, specs := ["reads", "writes"], indexedDecides }]
          continue
        cases := cases ++ [{
          receiver := actual,
          inputs := if op.isSome then [fieldTy, fieldTy] else [fieldTy],
          result := fieldTy, specs := if op.isSome then ["reads", "writes"] else ["writes"] }]
      else if isField then
        match actual with
        | .arr _ | .map .. =>
          if method != "Length" then break
          cases := cases ++ [{ receiver := actual, inputs := [], result := .int, specs := ["computes"] }]
        | .struct cls classArgs =>
          let some (_, result, _) := (ctx.types.fields cls classArgs).find? (·.1 == method) | break
          let specs := if ctx.types.isVarField cls method then ["reads"] else ["computes"]
          cases := cases ++ [{ receiver := actual, inputs := [], result, specs }]
        | _ => break
      else
        let .struct cls classArgs := actual | break
        let some owner := ctx.methodDecl? cls method | break
        let some signature := ctx.sig? s!"{owner}.{method}" | break
        let classVars := (ctx.types.sparams.lookup owner).getD []
        let own := signature.tparams.filter fun (n, _) => !classVars.any (·.1 == n)
        let methodVars := own.zipIdx.map fun ((_, b), i) => (s!"$operationMethod{i}", b)
        let methodRename := own.zip methodVars |>.map fun ((old, _), (name, bound)) => (old, Ty.param name bound)
        if signature.decides != bracket then break
        let some (supplied, omittedDefaults) := choiceCallInputs signature arguments | break
        -- An omitted value can determine a method instance at this call.
        -- A dictionary quantified over that parameter would instead have
        -- to check the default at every rigid instance, which can reject
        -- a valid source call (for example ?X:u=1 with no supplied u).
        let suppliedNames := arguments.filterMap fun
          | .decl _ n .. => if n.startsWith "?" then some (n.drop 1).toString else none
          | _ => none
        let npos := signature.params.length - signature.named.length
        if signature.named.zipIdx.any (fun ((n, _), i) => !suppliedNames.contains n &&
            signature.params[npos + i]!.params.any (fun v => own.any (·.1 == v))) then break
        let substitution := (classVars.map (·.1)).zip (ctx.types.upArgs cls classArgs owner)
        let inputs := supplied.map fun ty => ((ty.subst methodRename).subst substitution).subst ctx.types.tvars
        let result := ((signature.ret.subst methodRename).subst substitution).subst ctx.types.tvars
        let specs := (if signature.fx.isEmpty then ["computes"] else signature.fx) ++
          (if signature.decides then ["decides"] else []) ++
          (if signature.suspends then ["suspends"] else [])
        cases := cases ++ [{ receiver := actual, inputs, result, specs, methodVars, omittedDefaults }]
    if cases.length != plan.instances.length then
      -- A checked function-valued field fixes its result before its
      -- arguments are available, just as a monomorphic method does.
      if let .app _ member _ _ := call then
        if let some (Ty.struct name types) := (ops.knownTypes.find? (·.1 == member)).map (·.2) then
          if let some (arity, _) := FnValues.parseName name then
            if types.length == arity + 1 then
              ops := { ops with knownTypes := ops.knownTypes ++ [(call, types.getLast!)] }
      continue
    let bracket := if indexed then cases.any (·.indexedDecides) else bracket
    if cases.any (!·.methodVars.isEmpty) then
      if let some generic := choiceGenericOperation sourceCtx stem receiver receiverTy ops call cases then ops := generic
      continue
    let borrows := cases.any (·.omittedDefaults)
    let (initialPlan, operationReceiverTy) := if indexed then
      ChoiceTypes.extend ctx.types stem ops.plan (cases.map (·.receiver)) else (ops.plan, receiverTy)
    let mut extended := initialPlan
    let mut inputs : List Ty := []
    for j in List.range arguments.length do
      let (next, input) := ChoiceTypes.extend ctx.types stem extended (cases.map fun row => row.inputs[j]!)
      extended := next
      inputs := inputs ++ [input]
    let (finalPlan, result) := ChoiceTypes.extend ctx.types stem extended (cases.map (·.result))
    if setter.isSome then ops := choiceNumericConversions ctx stem { ops with plan := finalPlan }
    let specs := (if cases.any (·.specs.contains "suspends") then ["suspends"] else []) ++
      (if bracket then ["decides"] else []) ++
      (let effects := heapFx.filter fun k => cases.any fun row => (allowedFx row.specs).contains k
       if effects.isEmpty then ["computes"] else effects)
    let p0 : Pos := { line := 0, col := 0 }
    let canonical := cases.map fun row =>
      let types := row.receiver :: row.inputs
      let vars := Ty.mergeParamBounds ((types ++ [row.result]).flatMap Ty.paramsC)
      let rename := vars.zipIdx.map fun ((name, bound), i) => (name, Ty.param s!"$operationT{i}" bound)
      (types.map (·.subst rename), row.result.subst rename)
    let operationName := if indexed then "$indexSet:" ++ method ++ ((setter.getD none).map (":" ++ ·)).getD "" else
      if let some op := setter then "$set:" ++ method ++ ":" ++ op.getD "=" else
      if callable then "$invoke:" ++ method else if isField then "$field:" ++ method else method
    let context := if borrows then reprStr (choiceDefaultContext sourceCtx (.tuple p [])) else ""
    let labels := arguments.map fun | .decl _ n .. => n | _ => ""
    let familyKey := if !borrows && labels.all (· == "") then reprStr (operationName, specs, canonical) else
      reprStr (operationName, specs, canonical, labels, context)
    let family := s!"$choiceOperationDictionary{familyKey.hash}{if borrows then "$choiceDefault" else ""}"
    let names := "$operationReceiver" :: ((List.range arguments.length).map fun i => s!"$operationArgument{i}") ++ ["$operationResult"]
    let variables := names.map STy.name
    let tps := names.map fun n => ({ pos := p0, name := n, constraint := "type" } : TParam)
    let familyTy := STy.app family variables
    let params (types : List STy) : List SParam := types.zipIdx.map fun (ty, i) => { name := s!"$input{i}", ty }
    let values := (List.range (arguments.length + 1)).map fun i => SExpr.ident p0 s!"$input{i}"
    let iface := STop.classDef p0 family tps [] [] true [] []
      [.fn p0 "$apply" (params variables.dropLast) [] ("$abstract" :: specs) variables.getLast! (.tuple p0 [])]
    let applyFn := STop.fn p0 (family ++ "$apply")
      -- Pin the dictionary's class arguments before using an expected
      -- result, just as an ordinary method pins its receiver instance.
      ({ name := "$Self", ty := familyTy } :: params variables.dropLast) tps specs variables.getLast!
      (.app p0 (.member p0 (.ident p0 "$Self") "$apply") values bracket)
    let name := s!"{stem}$op{ops.params.length}"
    let ty := Ty.struct family (operationReceiverTy :: inputs ++ [result])
    let operation := if indexed then
      let op := setter.getD none
      let rhs := if op.isSome then SExpr.app p0 (.ident p0 "$withOld") [values[2]!, values[3]!] false else values[2]!
      SExpr.set p0 (.app p0 (.member p0 values[1]! method) [values[0]!] true) op rhs
    else if let some op := setter then
      let rhs := if op.isSome then SExpr.app p0 (.ident p0 "$withOld") [values[1]!, values[2]!] false
        else values[1]!
      SExpr.set p0 (.member p0 values.head! method) op rhs
    else if callable then SExpr.app p0 values.head! values.tail bracket else
      if isField then SExpr.member p0 values.head! method else
      .app p0 (.member p0 values.head! method) (choiceForwardArguments arguments values.tail) bracket
    let operation := if borrows then choiceDefaultContext sourceCtx operation else operation
    let mut definitions : List STop := [iface, applyFn]
    let mut bindings : List (List SExpr) := []
    for ((row, (canonicalInputs, canonicalRet)), i) in (cases.zip canonical).zipIdx do
      let impl := s!"{family}$case{i}"
      let vars := Ty.mergeParamBounds ((row.receiver :: row.inputs ++ [row.result]).flatMap Ty.paramsC)
      let canonicalVars := Ty.mergeParamBounds ((canonicalInputs ++ [canonicalRet]).flatMap Ty.paramsC)
      let implTps := canonicalVars.map fun (n, cmp) =>
        ({ pos := p0, name := n, constraint := if cmp then "comparable" else "type" } : TParam)
      let parentTy := STy.app family ((canonicalInputs ++ [canonicalRet]).map Ty.toSTy)
      definitions := definitions ++ [.classDef p0 impl implTps [] [parentTy] false [] []
        [.fn p0 "$apply" (params (canonicalInputs.map Ty.toSTy)) [] ("override" :: specs) canonicalRet.toSTy
          operation]]
      let valueTy := STy.app family ((row.receiver :: row.inputs ++ [row.result]).map Ty.toSTy)
      let value := SExpr.construct p impl (vars.map fun (n, _) => .name n) []
      bindings := bindings ++ [[.decl p name (some valueTy) false
        (.app p (.ident p "$choiceDictionary") [value] false)]]
    let sourceArguments := arguments.mapIdx fun i value =>
      let value := ops.rewrite (if !callable && !isField && setter.isNone then choiceArgumentValue value else value)
      if setter.isSome && i + 1 == arguments.length then ops.coercionContext value else value
    let sourceValues := if indexed then [sourceArguments[0]!, ops.rewrite receiver, sourceArguments[1]!] else
      ops.rewrite receiver :: sourceArguments
    let shape := SExpr.str p [.text (FnValues.shapeOf (arguments.length + 1) specs).name]
    let invocation := if indexed && (setter.getD none).isSome then
      let index := sourceArguments[0]!
      let object := ops.rewrite receiver
      let old := Choice.mapE (fun e =>
        if e == index then some (.ident p "$choiceIndexKey") else
        if e == object then some (.ident p "$choiceIndexObject") else none) sourceArguments[1]!
      SExpr.app p (.ident p "$choiceIndexedOperation") [shape, .ident p name, index, object, old, sourceArguments[2]!] bracket
    else SExpr.app p (.ident p "$choiceOperation") (shape :: .ident p name :: sourceValues) bracket
    ops := { ops with
      plan := finalPlan, params := ops.params ++ [(name, ty)],
      knownTypes := ops.knownTypes ++ [(call, result)],
      replacements := ops.replacements ++ [(key, invocation)],
      casePrelude := (ops.casePrelude.zip bindings).map fun (old, next) => old ++ next,
      extraFns := ops.extraFns ++ definitions }
  return ops

end OpenVerse.Front
