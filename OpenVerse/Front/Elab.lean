/-
  OpenVerse front end — elaboration of surface Verse into Verse Core.

  * Names are resolved: locals to slots of the function's frame, functions
    and constants to program indices. Verse forbids shadowing; so does this.
  * Types are checked (int, logic, char, string = []char, []t, ?t, tuples,
    void), bidirectionally so that `false` and `array{}` take their type
    from context.
  * Failure discipline (Book of Verse ch. 8): an expression that can fail
    must be in a failure context — an `if` condition, a `for` clause,
    `option{}`, `logic{}`, `not`, the left of `or`, or a `<decides>`
    function body. "Can fail" is computed by `Expr.mayFail`, the very
    analysis the `<decides>` soundness theorem (`Eval.no_fail`) is about.
  * Derived forms use `OpenVerse.Core.Derived` (`not`, `or`, `option{}`,
    `logic{}`), whose rollback laws are proved.
  * The result is checked with `Prog.check` (proved to imply the hypotheses of
    the core theorems) before anyone runs it.
-/
import OpenVerse.Core.Check
import OpenVerse.Core.Derived
import OpenVerse.Core.TypeCheck
import OpenVerse.Core.Control
import OpenVerse.Front.Parser

namespace OpenVerse.Front
open OpenVerse

inductive Ty where
  | int | logic | char | void
  /-- The bottom type, of `break`, `return` and `Err()`. -/
  | never
  | arr : Ty → Ty
  | opt : Ty → Ty
  | tup : List Ty → Ty
  /-- A struct type (nominal): its value is the tuple of its fields. -/
  | struct : String → Ty
  /-- An enum type (nominal): its value is the index of the enumerator. -/
  | enum : String → Ty
  /-- `[k]v`: in Verse Core, the array of its (key, value) pairs in insertion order. -/
  | map : Ty → Ty → Ty
  deriving Repr, Inhabited

partial def Ty.eqv : Ty → Ty → Bool
  | .int, .int | .logic, .logic | .char, .char | .void, .void | .never, .never => true
  | .arr a, .arr b => a.eqv b
  | .opt a, .opt b => a.eqv b
  | .tup as, .tup bs => as.length == bs.length && (as.zip bs).all fun (a, b) => a.eqv b
  | .struct a, .struct b => a == b
  | .enum a, .enum b => a == b
  | .map a b, .map c d => a.eqv c && b.eqv d
  | _, _ => false

instance : BEq Ty := ⟨Ty.eqv⟩

partial def Ty.show : Ty → String
  | .int => "int" | .logic => "logic" | .char => "char" | .void => "void" | .never => "false"
  | .arr .char => "string"
  | .arr t => "[]" ++ t.show
  | .opt t => "?" ++ t.show
  | .tup ts => "tuple(" ++ ", ".intercalate (ts.map Ty.show) ++ ")"
  | .struct n => n
  | .enum n => n
  | .map k v => "[" ++ k.show ++ "]" ++ v.show

def Ty.string : Ty := .arr .char

/-- The user-defined types of a program. -/
structure TyEnv where
  /-- Each struct: its fields in order (name, type, default value). -/
  structs : List (String × List (String × Ty × Option SExpr)) := []
  /-- Each enum: its enumerators in order. -/
  enums : List (String × List String) := []
  deriving Inhabited

def TyEnv.fields (env : TyEnv) (n : String) : List (String × Ty × Option SExpr) :=
  (env.structs.lookup n).getD []

/-- The struct names a type mentions (not looking inside those structs). -/
partial def Ty.structNames : Ty → List String
  | .struct n => [n]
  | .arr t | .opt t => t.structNames
  | .tup ts => ts.flatMap Ty.structNames
  | .map k v => k.structNames ++ v.structNames
  | _ => []

/-- A struct that contains itself, through any chain of fields (Verse Core
    types are finite trees, so such a struct has no representation). -/
def TyEnv.recursiveStruct? (env : TyEnv) : Option String :=
  let deps (n : String) : List String :=
    (env.fields n).flatMap fun (_, t, _) => t.structNames
  -- the structs reachable from `n` in at most `env.structs.length` steps
  let reach (n : String) : List String := Id.run do
    let mut seen : List String := []
    let mut frontier := deps n
    for _ in [0:env.structs.length + 1] do
      let new := frontier.filter (!seen.contains ·)
      seen := seen ++ new
      frontier := new.flatMap deps
    return seen
  (env.structs.map (·.1)).find? fun n => (reach n).contains n

/-- The Verse Core type of a front-end type (`false`, the bottom type, has
    no values; slots and signatures never have it). -/
partial def Ty.toVTy (env : TyEnv) : Ty → VTy
  | .int => .int
  | .logic => .logic
  | .char => .char
  | .void => VTy.void
  | .never => VTy.void
  | .arr t => .arr (t.toVTy env)
  | .opt t => .opt (t.toVTy env)
  | .tup ts => .tup (ts.map (Ty.toVTy env))
  | .struct n => .tup ((env.fields n).map fun (_, t, _) => t.toVTy env)
  | .enum _ => .int
  | .map k v => .arr (.tup [k.toVTy env, v.toVTy env])

structure Local where
  name    : String
  slot    : Nat
  ty      : Ty
  mutable : Bool

structure Sig where
  idx     : Nat
  name    : String
  params  : List Ty
  ret     : Ty
  decides : Bool
  isConst : Bool
  /-- The named parameters (the last ones of `params`): name and default. -/
  named   : List (String × Option SExpr) := []
  deriving Inhabited

structure Ctx where
  sigs    : List Sig
  /-- The functions' `<decides>` flags, as a program, for `Expr.mayFail`. -/
  sigProg : Prog
  locals  : List Local := []
  canFail : Bool := false
  inLoop  : Bool := false
  retTy   : Ty := .void
  types   : TyEnv := {}

structure ESt where
  nslots : Nat := 0
  /-- The type of each slot allocated so far (the certificate for `Prog.checkTypes`). -/
  slotTys : Array Ty := #[]

abbrev EM := StateT ESt (Except String)

/-- An elaborated expression and its type. -/
structure R where
  e  : Expr
  ty : Ty

/-- A new slot of the current frame, holding values of type `t`. -/
def fresh (t : Ty) : EM Nat :=
  modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push t })

def eerr (p : Pos) (msg : String) : EM α := throw s!"{p.show}: {msg}"

def builtins : List String :=
  ["Print", "ToString", "Floor", "Ceil", "Abs", "Min", "Max", "Quotient", "Mod", "Err"]

partial def resolveTy (env : TyEnv) (p : Pos) : STy → EM Ty
  | .name "int" => pure .int
  | .name "logic" => pure .logic
  | .name "char" => pure .char
  | .name "string" => pure Ty.string
  | .name "void" => pure .void
  | .name "float" => eerr p "float is not supported by openverse v1"
  | .name n =>
    if (env.structs.lookup n).isSome then pure (.struct n)
    else if (env.enums.lookup n).isSome then pure (.enum n)
    else eerr p s!"unknown type '{n}' (supported: int, logic, char, string, void, []t, ?t, tuple(…), and structs and enums)"
  | .arr t => return .arr (← resolveTy env p t)
  | .opt t => return .opt (← resolveTy env p t)
  | .tup [] => pure .void
  | .tup ts => return .tup (← ts.mapM (resolveTy env p))
  | .map k v => return .map (← resolveTy env p k) (← resolveTy env p v)

def Ctx.lookup (ctx : Ctx) (n : String) : Option Local := ctx.locals.find? (·.name == n)
def Ctx.sig? (ctx : Ctx) (n : String) : Option Sig := ctx.sigs.find? (·.name == n)

def p2 (op : Prim) (a b : Expr) : Expr := .prim op [a, b]

/-- Convert `r` to type `target`: equal types, `false` (bottom) to anything,
    and anything to `void` (Book of Verse: "void accepts any value"). -/
def coerce (p : Pos) (r : R) (target : Ty) : EM Expr :=
  if r.ty == target || r.ty == .never then pure r.e
  else if target == .void then pure (.seq r.e (.lit .void))
  else eerr p s!"expected {target.show}, found {r.ty.show}"

/-- The type of a two-branch construct. -/
def join (p : Pos) (a b : Ty) (exp : Option Ty) : EM Ty :=
  match exp with
  | some .void => pure .void
  | _ =>
    if a == .never then pure b
    else if b == .never then pure a
    else if a == b then pure a
    else eerr p s!"the branches have different types: {a.show} and {b.show}"

def isComparable : Ty → Bool
  | .never => false
  | _ => true

/-- `M[k]` on the map in slot `tm` with the key in slot `tk`: the value of the
    first pair whose key equals `k` (fails when there is none). `tp` is a
    slot for the pairs. -/
def mapLookup (tm tk tp : Nat) : Expr :=
  .prim .index [.forE tp (.local tm) (.prim .eq [.prim (.tupGet 0) [.local tp], .local tk])
      (.prim (.tupGet 1) [.local tp]), .lit (.int 0)]

/-- The position of key `k` (slot `tk`) in the map in slot `tm` (fails when absent). -/
def mapFind (tm tk ti : Nat) : Expr :=
  .prim .index [.forE ti (.prim .range [.lit (.int 0), .prim .sub [.prim .len [.local tm], .lit (.int 1)]])
      (.prim .eq [.prim (.tupGet 0) [.prim .index [.local tm, .local ti]], .local tk]) (.local ti),
    .lit (.int 0)]

/-- Insert or update `(k, v)` (slots `tk`, `tv`) in the map in slot `tm`, in
    place when the key exists, at the end otherwise (Book of Verse §9.3). -/
def mapPut (tm tk tv ti tidx : Nat) : Expr :=
  let pair := Expr.prim .mkTup [.local tk, .local tv]
  .ite (.seq (.assign tidx (mapFind tm tk ti)) (.assign tm (.prim .arrSet [.local tm, .local tidx, pair])))
    (.lit .void)
    (.seq (.assign tm (.prim .concat [.local tm, .prim .mkArr [pair]])) (.lit .void))

/-- The position of a field in its struct. -/
def fieldIndex (fs : List (String × Ty × Option SExpr)) (f : String) : Option (Nat × Ty) :=
  ((fs.zip (List.range fs.length)).find? (·.1.1 == f)).map fun ((_, t, _), k) => (k, t)

/-- `ToString` for interpolation. -/
def toStringOf (p : Pos) (r : R) : EM Expr :=
  match r.ty with
  | .int | .char => pure (.prim .toStr [r.e])
  | .arr .char => pure r.e
  | t => eerr p s!"no ToString for {t.show} (Verse defines it for int, char and string)"

mutual
partial def elabE (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  match se with
  | .int p n =>
    if !Int64.inRange n then eerr p s!"integer literal {n} does not fit in 64 bits"
    return ⟨.lit (.int n), .int⟩
  | .char _ c => return ⟨.lit (.char c), .char⟩
  | .str p parts =>
    let pieces ← parts.mapM fun part => match part with
      | .text s => pure (Expr.lit (Value.ofString s))
      | .code e => do toStringOf e.pos (← elabE ctx e none)
    let _ := p
    match pieces with
    | [] => return ⟨.lit (Value.ofString ""), Ty.string⟩
    | e :: es => return ⟨es.foldl (fun a b => p2 .concat a b) e, Ty.string⟩
  | .ident p n =>
    match n with
    | "true" => return ⟨.lit (.logic true), .logic⟩
    | "false" =>
      match exp with
      | some (.opt t) => return ⟨.lit .none, .opt t⟩
      | some (.arr t) => return ⟨.lit (.arr []), .arr t⟩
      | some .void => return ⟨.lit .void, .void⟩
      | _ => return ⟨.lit (.logic false), .logic⟩
    | _ =>
      match ctx.lookup n with
      | some l => return ⟨.local l.slot, l.ty⟩
      | none => match ctx.sig? n with
        | some s =>
          if s.isConst then return ⟨.call s.idx [], s.ret⟩
          else eerr p s!"'{n}' is a function: call it with {n}(…)"
        | none => eerr p s!"unknown identifier '{n}'"
  | .app p f args bracket => elabApp ctx p f args bracket exp
  | .member p (.ident _ n) m =>
    match ctx.lookup n, ctx.types.enums.lookup n with
    | none, some vals =>
      -- `color.Red`: an enumerator
      match vals.idxOf? m with
      | some k => return ⟨.lit (.int k), .enum n⟩
      | none => eerr p s!"enum {n} has no value '{m}'"
    | _, _ => elabMember ctx p (← elabE ctx (.ident p n) none) m
  | .member p e m => elabMember ctx p (← elabE ctx e none) m
  | .construct p name args => elabConstruct ctx p name args
  | .mapLit p entries => elabMapLit ctx p entries exp
  | .structDef p _ | .enumDef p _ => eerr p "struct and enum definitions must be at the top level"
  | .query p e =>
    let r ← elabE ctx e none
    match r.ty with
    | .opt t => return ⟨.prim .query [r.e], t⟩
    | .logic => return ⟨.prim .query [r.e], .logic⟩
    | t => eerr p s!"'?' needs an option or logic, found {t.show}"
  | .neg p e =>
    let r ← elabE ctx e (some .int)
    if r.ty != .int then eerr p s!"unary '-' needs an int, found {r.ty.show}"
    return ⟨.prim .neg [r.e], .int⟩
  | .notE _ e =>
    let r ← elabE { ctx with canFail := true } e none
    return ⟨Expr.notE r.e, .void⟩
  | .bin p "/" _ _ =>
    eerr p "integer '/' gives a rational; write Floor(X / Y), Ceil(X / Y) or Quotient[X, Y]"
  | .bin p op a b =>
    let ra ← elabE ctx a none
    let rb ← elabE ctx b (some ra.ty)
    match op, ra.ty, rb.ty with
    | "+", .int, .int => return ⟨p2 .add ra.e rb.e, .int⟩
    | "-", .int, .int => return ⟨p2 .sub ra.e rb.e, .int⟩
    | "*", .int, .int => return ⟨p2 .mul ra.e rb.e, .int⟩
    | "+", .arr t, .arr u =>
      if t == u then return ⟨p2 .concat ra.e rb.e, .arr t⟩
      else eerr p s!"cannot concatenate {ra.ty.show} and {rb.ty.show}"
    | _, ta, tb => eerr p s!"no operator '{op}' for {ta.show} and {tb.show}"
  | .cmp p a rest => elabCmp ctx p a rest
  | .andE _ a b =>
    -- each operand is its own scope: names defined in `a` are not visible in
    -- `b`, and names from either side do not escape the `and`
    let (ra, _) ← elabStmt ctx a none
    let (rb, _) ← elabStmt ctx b exp
    return ⟨Expr.andE ra.e rb.e, rb.ty⟩
  | .orE p a b =>
    let ra ← elabE { ctx with canFail := true } a exp
    let rb ← elabE ctx b (exp.getD ra.ty)
    let ty ← join p ra.ty rb.ty exp
    let t ← fresh ty
    return ⟨Expr.orE t (← coerce p ra ty) (← coerce p rb ty), ty⟩
  | .range p _ _ => eerr p "a range a..b can only be the source of a for clause"
  | .tuple _ [] => return ⟨.lit .void, .void⟩
  | .tuple _ es =>
    let exps : List (Option Ty) := match exp with
      | some (.tup ts) => if ts.length == es.length then ts.map some else es.map fun _ => none
      | _ => es.map fun _ => none
    let rs ← (es.zip exps).mapM fun (e, t) => elabE ctx e t
    return ⟨.prim .mkTup (rs.map (·.e)), .tup (rs.map (·.ty))⟩
  | .block _ ss =>
    let (r, _) ← elabSeq ctx ss exp
    return r
  | .arrayLit p es =>
    let elemExp : Option Ty := match exp with
      | some (.arr t) => some t
      | _ => none
    match es with
    | [] => match elemExp with
      | some t => return ⟨.lit (.arr []), .arr t⟩
      | none => eerr p "the type of an empty array{} must be given (e.g. X:[]int = array{})"
    | e :: rest =>
      let r ← elabE ctx e elemExp
      let t := elemExp.getD r.ty
      let first ← coerce e.pos r t
      let others ← rest.mapM fun e' => do coerce e'.pos (← elabE ctx e' (some t)) t
      return ⟨.prim .mkArr (first :: others), .arr t⟩
  | .optionLit _ e =>
    let inner : Option Ty := match exp with
      | some (.opt t) => some t
      | _ => none
    let r ← elabE { ctx with canFail := true } e inner
    let t ← fresh r.ty
    return ⟨Expr.optionE t r.e, .opt r.ty⟩
  | .logicLit p e =>
    let r ← elabE { ctx with canFail := true } e none
    if !r.e.mayFail ctx.sigProg then eerr p "logic{…} needs an expression that can fail"
    return ⟨Expr.logicE r.e, .logic⟩
  | .ite p conds thenE elseE =>
    let (rc, ctxT) ← elabSeq { ctx with canFail := true } conds none
    if !rc.e.mayFail ctx.sigProg then
      eerr p "the condition of this if cannot fail (Verse requires a failable condition)"
    let thenCtx := { ctxT with canFail := ctx.canFail }
    match elseE with
    | none =>
      let rt ← elabE thenCtx thenE (some .void)
      return ⟨.ite rc.e (← coerce p rt .void) (.lit .void), .void⟩
    | some ee =>
      let rt ← elabE thenCtx thenE exp
      let re ← elabE ctx ee (exp.getD rt.ty)
      let ty ← join p rt.ty re.ty exp
      return ⟨.ite rc.e (← coerce p rt ty) (← coerce p re ty), ty⟩
  | .forE p clauses body => elabFor ctx p clauses body
  | .gen p _ _ _ => eerr p "a generator X : source can only appear in a for clause"
  | .loop _ body =>
    let r ← elabE { ctx with inLoop := true } body none
    return ⟨.loop r.e, .void⟩
  | .brk p =>
    if !ctx.inLoop then eerr p "break is only allowed inside loop (not for)"
    return ⟨.brk, .never⟩
  | .ret p none =>
    if ctx.retTy != .void then eerr p s!"return needs a value of type {ctx.retTy.show}"
    return ⟨.ret (.lit .void), .never⟩
  | .ret p (some e) =>
    let r ← elabE ctx e (some ctx.retTy)
    return ⟨.ret (← coerce p r ctx.retTy), .never⟩
  | .caseE p scrut arms => elabCase ctx p scrut arms exp
  | .decl p _ _ _ _ =>
    let (r, _) ← elabStmt ctx se exp
    let _ := p
    return r
  | .set p lhs op rhs => elabSet ctx p lhs op rhs

/-- A statement: like `elabE`, but a declaration extends the scope. Also
    enforces the failure discipline. -/
partial def elabStmt (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  let (r, ctx') ← match se with
    | .decl p n sty isVar rhs => do
      if ctx.lookup n |>.isSome then
        eerr p s!"'{n}' is already defined; Verse does not allow shadowing (use set {n} = … for a var)"
      if (ctx.sig? n).isSome || builtins.contains n then
        eerr p s!"'{n}' is already the name of a function or constant"
      let ty? ← sty.mapM (resolveTy ctx.types p)
      let r ← elabE ctx rhs ty?
      let ty := ty?.getD r.ty
      if ty == .never then eerr p s!"cannot infer the type of '{n}'"
      let e ← coerce p r ty
      let slot ← fresh ty
      pure (⟨.assign slot e, ty⟩,
        { ctx with locals := { name := n, slot, ty, mutable := isVar } :: ctx.locals })
    | _ => do pure (← elabE ctx se exp, ctx)
  if !ctx.canFail && r.e.mayFail ctx.sigProg then
    eerr se.pos ("this expression can fail, but it is not in a failure context (an if " ++
      "condition, a for clause, option{…}, logic{…}, not, the left of or, or a <decides> function)")
  return (r, ctx')

/-- A sequence of statements, threading the scope; the value is the last one's. -/
partial def elabSeq (ctx : Ctx) (ss : List SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  match ss with
  | [] => return (⟨.lit .void, .void⟩, ctx)
  | [s] => elabStmt ctx s exp
  | s :: rest =>
    let (r, ctx') ← elabStmt ctx s none
    let (r2, ctx'') ← elabSeq ctx' rest exp
    return (⟨.seq r.e r2.e, r2.ty⟩, ctx'')

partial def elabArgs (ctx : Ctx) (p : Pos) (args : List SExpr) (tys : List Ty) : EM (List Expr) := do
  if args.length != tys.length then
    eerr p s!"expected {tys.length} argument(s), found {args.length}"
  (args.zip tys).mapM fun (a, t) => do coerce a.pos (← elabE ctx a (some t)) t

partial def elabInts (ctx : Ctx) (p : Pos) (args : List SExpr) : EM (List Expr) :=
  elabArgs ctx p args (args.map fun _ => .int)

partial def elabApp (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM R := do
  let needBracket (name : String) : EM Unit := do
    if !bracket then eerr p s!"{name} can fail: call it with {name}[…]"
  match f with
  | .ident _ name =>
    match ctx.lookup name with
    | some l => elabIndexLike ctx p ⟨.local l.slot, l.ty⟩ args bracket
    | none =>
    match name with
    | "Print" =>
      let es ← elabArgs ctx p args [Ty.string]
      return ⟨.print es.head!, .void⟩
    | "ToString" =>
      match args with
      | [a] => return ⟨← toStringOf p (← elabE ctx a none), Ty.string⟩
      | _ => eerr p "ToString takes one argument"
    | "Abs" => return ⟨.prim .abs (← elabInts ctx p args), .int⟩
    | "Floor" | "Ceil" =>
      match args with
      | [.bin _ "/" a b] =>
        let es ← elabInts ctx p [a, b]
        return ⟨.prim (if name == "Floor" then .floorDiv else .ceilDiv) es, .int⟩
      | _ => eerr p s!"openverse v1 supports {name}(X / Y) on ints only"
    | "Quotient" => needBracket name; return ⟨.prim .quotient (← elabInts ctx p args), .int⟩
    | "Mod" => needBracket name; return ⟨.prim .modulo (← elabInts ctx p args), .int⟩
    | "Min" | "Max" =>
      let es ← elabInts ctx p args
      let ta ← fresh .int
      let tb ← fresh .int
      let op := if name == "Min" then Prim.le else Prim.ge
      return ⟨.seq (.assign ta es[0]!) (.seq (.assign tb es[1]!)
        (.ite (p2 op (.local ta) (.local tb)) (.local ta) (.local tb))), .int⟩
    | "Err" => return ⟨.prim .userErr [], .never⟩
    | _ =>
      match ctx.sig? name with
      | some s =>
        if s.isConst then
          elabIndexLike ctx p ⟨.call s.idx [], s.ret⟩ args bracket
        else
          if s.decides && !bracket then eerr p s!"{name} is <decides>: call it with {name}[…]"
          let _ := exp
          let isNamed : SExpr → Bool
            | .decl _ n _ _ _ => n.startsWith "?"
            | _ => false
          if s.named.isEmpty && !args.any isNamed then
            let es ← elabArgs ctx p args s.params
            return ⟨.call s.idx es, s.ret⟩
          -- named arguments: evaluate positional arguments left to right, then named ones as
          -- written, then the defaults of those omitted (Book of Verse §2.5), into temporaries
          let npos := s.params.length - s.named.length
          let pos := args.filter (!isNamed ·)
          let named := args.filterMap fun a => match a with
            | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
            | _ => none
          if pos.length != npos then eerr p s!"{name} takes {npos} positional argument(s), found {pos.length}"
          for (ap, n, _) in named do
            if (s.named.find? (·.1 == n)).isNone then eerr ap s!"{name} has no parameter ?{n}"
          let ptys := s.params.toArray
          let mut steps : Array Expr := #[]
          let mut slots : Array (Option Nat) := Array.replicate s.params.length none
          for (a, k) in pos.zip (List.range npos) do
            let t := ptys[k]!
            let ta ← fresh t
            steps := steps.push (.assign ta (← coerce a.pos (← elabE ctx a (some t)) t))
            slots := slots.set! k (some ta)
          for (ap, n, rhs) in named do
            let k := npos + (s.named.findIdx? (·.1 == n)).get!
            let t := ptys[k]!
            let ta ← fresh t
            steps := steps.push (.assign ta (← coerce ap (← elabE ctx rhs (some t)) t))
            slots := slots.set! k (some ta)
          for ((n, dflt), j) in s.named.zip (List.range s.named.length) do
            let k := npos + j
            if slots[k]!.isNone then
              let some d := dflt | eerr p s!"{name} needs the argument ?{n}, which has no default"
              let t := ptys[k]!
              let ta ← fresh t
              steps := steps.push (.assign ta (← coerce p (← elabE { ctx with locals := [] } d (some t)) t))
              slots := slots.set! k (some ta)
          let call := Expr.call s.idx (slots.toList.map fun o => Expr.local o.get!)
          return ⟨steps.toList.foldr Expr.seq call, s.ret⟩
      | none => eerr p s!"unknown function '{name}'"
  | .member _ obj m => elabMethod ctx p (← elabE ctx obj none) m args bracket
  | _ => elabIndexLike ctx p (← elabE ctx f none) args bracket

/-- The failable array methods of the Book of Verse (§9.1):
    `A.Slice[i, j]`, `A.Slice[i]`, `A.Find[x]`, `A.RemoveElement[i]`,
    `A.ReplaceElement[i, x]`, `A.Insert[i, B]`. Each fails when an index is
    out of range (or, for `Find`, when there is no such element). -/
partial def elabMethod (ctx : Ctx) (p : Pos) (r : R) (m : String) (args : List SExpr) (bracket : Bool) :
    EM R := do
  let .arr t := r.ty | eerr p s!"{r.ty.show} has no method '{m}'"
  if !bracket then eerr p s!"{m} can fail: call it with A.{m}[…]"
  let ta ← fresh r.ty
  let len := Expr.prim .len [.local ta]
  let int (i : Int) : Expr := .lit (.int i)
  -- the elements of A at indices lo, …, hi - 1 (lo ≤ hi known)
  let slice (lo hi : Expr) : EM Expr := do
    let ti ← fresh .int
    let tx ← fresh t
    return .forE ti (.prim .range [lo, p2 .sub hi (int 1)]) (.assign tx (p2 .index (.local ta) (.local ti)))
      (.local tx)
  let start := Expr.assign ta r.e
  match m, args with
  | "Slice", [a, b] =>
    let es ← elabInts ctx p [a, b]
    let tlo ← fresh .int
    let thi ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (.seq (p2 .le (.local tlo) (.local thi))
      (p2 .le (.local thi) len))
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq (.assign thi es[1]!) (.seq chk
      (← slice (.local tlo) (.local thi))))), r.ty⟩
  | "Slice", [a] =>
    let es ← elabInts ctx p [a]
    let tlo ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tlo)) (p2 .le (.local tlo) len)
    return ⟨.seq start (.seq (.assign tlo es[0]!) (.seq chk (← slice (.local tlo) len))), r.ty⟩
  | "Find", [x] =>
    let rx ← elabE ctx x (some t)
    let tx ← fresh t
    let ti ← fresh .int
    let found := Expr.forE ti (.prim .range [int 0, p2 .sub len (int 1)])
      (p2 .eq (p2 .index (.local ta) (.local ti)) (.local tx)) (.local ti)
    return ⟨.seq start (.seq (.assign tx (← coerce p rx t)) (p2 .index found (int 0))), .int⟩
  | "RemoveElement", [i] =>
    let es ← elabInts ctx p [i]
    let tk ← fresh .int
    let chk := Expr.seq (p2 .le (int 0) (.local tk)) (p2 .lt (.local tk) len)
    return ⟨.seq start (.seq (.assign tk es[0]!) (.seq chk
      (p2 .concat (← slice (int 0) (.local tk)) (← slice (p2 .add (.local tk) (int 1)) len)))), r.ty⟩
  | "ReplaceElement", [i, x] =>
    let es ← elabInts ctx p [i]
    let rx ← elabE ctx x (some t)
    return ⟨.seq start (.prim .arrSet [.local ta, es[0]!, ← coerce p rx t]), r.ty⟩
  | "Insert", [i, b] =>
    let es ← elabInts ctx p [i]
    let rb ← elabE ctx b (some r.ty)
    let tk ← fresh .int
    let tb ← fresh r.ty
    let chk := Expr.seq (p2 .le (int 0) (.local tk)) (p2 .le (.local tk) len)
    return ⟨.seq start (.seq (.assign tk es[0]!) (.seq (.assign tb (← coerce p rb r.ty)) (.seq chk
      (p2 .concat (p2 .concat (← slice (int 0) (.local tk)) (.local tb)) (← slice (.local tk) len))))), r.ty⟩
  | _, _ => eerr p s!"unknown array method '{m}' with {args.length} argument(s) (openverse supports Slice, Find, RemoveElement, ReplaceElement, Insert)"

/-- `A[i]` on an array (failable) or `T(k)` on a tuple. -/
partial def elabIndexLike (ctx : Ctx) (p : Pos) (r : R) (args : List SExpr) (bracket : Bool) : EM R := do
  match r.ty, args, bracket with
  | .arr t, [i], true =>
    let ri ← elabE ctx i (some .int)
    if ri.ty != .int then eerr p s!"an array index must be an int, found {ri.ty.show}"
    return ⟨p2 .index r.e ri.e, t⟩
  | .map kt vt, [k], true =>
    let tm ← fresh r.ty
    let rk ← elabE ctx k (some kt)
    let tk ← fresh kt
    let tp ← fresh (.tup [kt, vt])
    return ⟨.seq (.assign tm r.e) (.seq (.assign tk (← coerce p rk kt)) (mapLookup tm tk tp)), vt⟩
  | .tup ts, [.int _ k], false =>
    if k < 0 || k.toNat ≥ ts.length then eerr p s!"tuple index {k} out of range"
    return ⟨.prim (.tupGet k.toNat) [r.e], ts[k.toNat]!⟩
  | t, _, _ => eerr p s!"cannot call or index a value of type {t.show}"

partial def elabCmp (ctx : Ctx) (p : Pos) (a : SExpr) (rest : List (String × SExpr)) : EM R := do
  let opOf : String → Prim
    | "=" => .eq | "<>" => .ne | "<" => .lt | "<=" => .le | ">" => .gt | _ => .ge
  let checkTys (op : String) (ta tb : Ty) : EM Unit := do
    if op == "=" || op == "<>" then
      if !isComparable ta || !isComparable tb then eerr p "these values cannot be compared"
    else if !((ta == .int && tb == .int) || (ta == .char && tb == .char)) then
      eerr p s!"'{op}' compares ints or chars, found {ta.show} and {tb.show}"
  let ra ← elabE ctx a none
  match rest with
  | [(op, b)] =>
    let rb ← elabE ctx b (some ra.ty)
    checkTys op ra.ty rb.ty
    return ⟨p2 (opOf op) ra.e rb.e, ra.ty⟩
  | _ =>
    -- a chain: each operand is evaluated once, every adjacent pair is checked,
    -- and the result is the leftmost operand (Book of Verse §5.4)
    let t0 ← fresh ra.ty
    let mut prev := t0
    let mut prevTy := ra.ty
    let mut steps : Array Expr := #[.assign t0 ra.e]
    for (op, b) in rest do
      let rb ← elabE ctx b (some prevTy)
      checkTys op prevTy rb.ty
      let tb ← fresh rb.ty
      steps := steps.push (.assign tb rb.e)
      steps := steps.push (p2 (opOf op) (.local prev) (.local tb))
      prev := tb
      prevTy := rb.ty
    return ⟨steps.foldr Expr.seq (.local t0), ra.ty⟩

partial def elabSet (ctx : Ctx) (p : Pos) (lhs : SExpr) (op : Option String) (rhs : SExpr) : EM R := do
  let combine (old : Expr) (ty : Ty) (o : String) (new : R) : EM Expr :=
    match o, ty, new.ty with
    | "+", .int, .int => pure (p2 .add old new.e)
    | "-", .int, .int => pure (p2 .sub old new.e)
    | "*", .int, .int => pure (p2 .mul old new.e)
    | "+", .arr t, .arr u => if t == u then pure (p2 .concat old new.e)
        else eerr p s!"cannot concatenate {ty.show} and {new.ty.show}"
    | "/", .int, _ => eerr p "set /= is not defined on int (integer division can fail)"
    | _, _, _ => eerr p s!"no operator '{o}=' for {ty.show} and {new.ty.show}"
  let mutableLocal (n : String) : EM Local := do
    match ctx.lookup n with
    | some l => if l.mutable then pure l else eerr p s!"'{n}' is not a var; declare it with var {n}:t = …"
    | none => eerr p s!"unknown variable '{n}'"
  match lhs with
  | .ident _ n =>
    let l ← mutableLocal n
    let r ← elabE ctx rhs (some l.ty)
    let v ← match op with
      | none => coerce p r l.ty
      | some o => combine (.local l.slot) l.ty o r
    return ⟨.assign l.slot v, l.ty⟩
  | .app _ (.ident _ n) [k] true =>
    let l ← mutableLocal n
    match l.ty with
    | .map kt vt =>
      let rk ← elabE ctx k (some kt)
      let tk ← fresh kt
      let tp ← fresh (.tup [kt, vt])
      let r ← elabE ctx rhs (some vt)
      let v ← match op with
        | none => coerce p r vt
        -- `set M[k] op= v` fails when k is not a key (Book of Verse §9.3)
        | some o => combine (mapLookup l.slot tk tp) vt o r
      let tv ← fresh vt
      let ti ← fresh .int
      let tidx ← fresh .int
      return ⟨.seq (.assign tk (← coerce p rk kt)) (.seq (.assign tv v)
        (.seq (mapPut l.slot tk tv ti tidx) (.local tv))), vt⟩
    | .arr t =>
      let i := k
      let ri ← elabE ctx i (some .int)
      if ri.ty != .int then eerr p "an array index must be an int"
      let ti ← fresh .int
      let tv ← fresh t
      let r ← elabE ctx rhs (some t)
      let v ← match op with
        | none => coerce p r t
        | some o => combine (p2 .index (.local l.slot) (.local ti)) t o r
      -- `set A[i] = v` fails out of range and returns `v` (Book of Verse §3.3)
      return ⟨.seq (.assign ti ri.e)
        (.seq (.assign l.slot (.prim .arrSet [.local l.slot, .local ti, .assign tv v])) (.local tv)), t⟩
    | ty => eerr p s!"cannot index a value of type {ty.show}"
  | .member _ (.ident _ n) f =>
    let l ← mutableLocal n
    match l.ty with
    | .struct sn =>
      let fs := ctx.types.fields sn
      match fieldIndex fs f with
      | some (k, t) =>
        let r ← elabE ctx rhs (some t)
        let v ← match op with
          | none => coerce p r t
          | some o => combine (.prim (.tupGet k) [.local l.slot]) t o r
        let tv ← fresh t
        -- the struct is rebuilt with field k replaced; `set` returns the new field value
        let parts := (List.range fs.length).map fun i =>
          if i == k then Expr.assign tv v else Expr.prim (.tupGet i) [.local l.slot]
        return ⟨.seq (.assign l.slot (.prim .mkTup parts)) (.local tv), t⟩
      | none => eerr p s!"struct {sn} has no field '{f}'"
    | ty => eerr p s!"{ty.show} has no field '{f}'"
  | _ => eerr p "openverse v1 supports set X = …, set A[i] = … and set S.F = …"

/-- `for`: clauses are generators, bindings and filters; each generator opens
    a nested `forE`, and nested results are flattened (cartesian product,
    leftmost outermost). The clauses are a failure context; the body is not. -/
partial def elabFor (ctx : Ctx) (p : Pos) (clauses : List SExpr) (body : SExpr) : EM R := do
  -- split into groups: [filters before the first generator], then (generator, filters)…
  let isGen : SExpr → Bool
    | .gen .. => true
    | .decl _ _ none false (.range ..) => true
    | _ => false
  let pre := clauses.takeWhile (!isGen ·)
  let rest := clauses.dropWhile (!isGen ·)
  let rec groups : List SExpr → List (SExpr × List SExpr)
    | [] => []
    | g :: cs =>
      let fs := cs.takeWhile (!isGen ·)
      (g, fs) :: groups (cs.dropWhile (!isGen ·))
  let gs := groups rest
  let bodyCtx (c : Ctx) : Ctx := { c with canFail := ctx.canFail, inLoop := false }
  -- elaborate the filters of one generator (in a failure context)
  let elabFilters (c : Ctx) (fs : List SExpr) : EM (Expr × Ctx) := do
    match fs with
    | [] => return (.lit (.logic true), c)
    | _ =>
      let (r, c') ← elabSeq { c with canFail := true } fs none
      return (r.e, c')
  let rec build (c : Ctx) (gs : List (SExpr × List SExpr)) : EM R := do
    match gs with
    | [] =>
      let r ← elabE (bodyCtx c) body none
      return r
    | (g, fs) :: more =>
      let declare (c : Ctx) (n : String) (ty : Ty) : EM (Nat × Ctx) := do
        if c.lookup n |>.isSome then eerr g.pos s!"'{n}' is already defined"
        let slot ← fresh ty
        return (slot, { c with locals := { name := n, slot, ty, mutable := false } :: c.locals })
      -- the source: evaluated before the iterations; a failing source gives no iterations
      let (slot, src, c1, pre) ← match g with
        | .decl gp n none false (.range _ lo hi) => do
          let es ← elabInts { c with canFail := true } gp [lo, hi]
          let (slot, c1) ← declare c n .int
          pure (slot, Expr.prim .range es, c1, Expr.lit (.logic true))
        | .gen gp x idx srcE => do
          let rs ← elabE { c with canFail := true } srcE none
          match rs.ty with
          | .map kt vt =>
            -- `for (V : M)` and `for (K -> V : M)`: over the (key, value) pairs
            let tmp ← fresh rs.ty
            let src := if rs.e.mayFail ctx.sigProg then
                Expr.orE tmp rs.e (.lit (.arr [])) else rs.e
            let tp ← fresh (.tup [kt, vt])
            let (pre, c1) ← match idx with
              | none => do
                let (xs, c1) ← declare c x vt
                pure (Expr.assign xs (.prim (.tupGet 1) [.local tp]), c1)
              | some i => do
                let (is, c1) ← declare c i kt
                let (xs, c2) ← declare c1 x vt
                pure (Expr.seq (.assign is (.prim (.tupGet 0) [.local tp]))
                  (.assign xs (.prim (.tupGet 1) [.local tp])), c2)
            pure (tp, src, c1, pre)
          | _ =>
          match idx with
          | some i => do
            -- `I -> X : A`: iterate over the indices of A
            let ty ← match rs.ty with
              | .arr t => pure t
              | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
            let tmp ← fresh rs.ty
            let src0 := if rs.e.mayFail ctx.sigProg then
                Expr.orE tmp rs.e (.lit (.arr [])) else rs.e
            let ta ← fresh rs.ty
            let (islot, c1) ← declare c i .int
            let (xslot, c2) ← declare c1 x ty
            let src := Expr.seq (.assign ta src0)
              (.prim .range [.lit (.int 0), p2 .sub (.prim .len [.local ta]) (.lit (.int 1))])
            pure (islot, src, c2, Expr.assign xslot (p2 .index (.local ta) (.local islot)))
          | none => do
          let ty ← match rs.ty with
            | .arr t => pure t
            | t => eerr gp s!"a for generator needs an array, string or map, found {t.show}"
          let tmp ← fresh rs.ty
          let src := if rs.e.mayFail ctx.sigProg then
              Expr.orE tmp rs.e (.lit (.arr [])) else rs.e
          let (slot, c1) ← declare c x ty
          pure (slot, src, c1, Expr.lit (.logic true))
        | _ => eerr g.pos "bad for clause"
      let (filt, c2) ← elabFilters c1 fs
      let filt := if fs.isEmpty then pre else
        match pre with
        | .lit _ => filt
        | e => .seq e filt
      let inner ← build c2 more
      let loopE := Expr.forE slot src filt inner.e
      match more with
      | [] => return ⟨loopE, .arr inner.ty⟩
      | _ =>
        match inner.ty with
        | .arr t => return ⟨.prim .flatten [loopE], .arr t⟩
        | _ => eerr p "internal: nested for"
  match pre with
  | [] => build ctx gs
  | _ =>
    -- filters before any generator: iterate once over a one-element array
    let (filt, c1) ← elabFilters ctx pre
    let slot ← fresh .void
    let inner ← build c1 gs
    match gs with
    | [] => return ⟨.forE slot (.lit (.arr [.tup []])) filt inner.e, .arr inner.ty⟩
    | _ =>
      match inner.ty with
      | .arr t => return ⟨.prim .flatten [.forE slot (.lit (.arr [.tup []])) filt inner.e], .arr t⟩
      | _ => eerr p "internal: nested for"

/-- `e.m`: `.Length` of an array or string, or a field of a struct. -/
partial def elabMember (ctx : Ctx) (p : Pos) (r : R) (m : String) : EM R := do
  match r.ty, m with
  | .arr _, "Length" => return ⟨.prim .len [r.e], .int⟩
  | .map _ _, "Length" => return ⟨.prim .len [r.e], .int⟩
  | .struct sn, f =>
    match fieldIndex (ctx.types.fields sn) f with
    | some (k, t) => return ⟨.prim (.tupGet k) [r.e], t⟩
    | none => eerr p s!"struct {sn} has no field '{f}'"
  | t, m => eerr p s!"{t.show} has no member '{m}'"

/-- `name{F := e, …}`: the struct's fields in declaration order; omitted
    fields take their default values. -/
partial def elabConstruct (ctx : Ctx) (p : Pos) (name : String) (args : List SExpr) : EM R := do
  let some fs := ctx.types.structs.lookup name
    | eerr p s!"unknown struct '{name}'"
  let given ← args.mapM fun a => match a with
    | .decl _ f none false rhs => pure (f, rhs)
    | a => eerr a.pos "a struct field is given as Name := value"
  for (f, _) in given do
    if (fs.find? (·.1 == f)).isNone then eerr p s!"struct {name} has no field '{f}'"
  let es ← fs.mapM fun (f, t, dflt) => do
    match given.lookup f, dflt with
    | some rhs, _ => coerce p (← elabE ctx rhs (some t)) t
    | none, some d => coerce p (← elabE { ctx with locals := [] } d (some t)) t
    | none, none => eerr p s!"field '{f}' of {name} has no default value and must be given"
  return ⟨.prim .mkTup es, .struct name⟩

/-- `map{k₁ => v₁, …}`: entries are evaluated in order; a key given twice
    keeps its last value, at the position of its last occurrence (Book of
    Verse §9.3). -/
partial def elabMapLit (ctx : Ctx) (p : Pos) (entries : List (SExpr × SExpr)) (exp : Option Ty) : EM R := do
  let (kt?, vt?) := match exp with
    | some (.map k v) => (some k, some v)
    | _ => (none, none)
  match entries with
  | [] =>
    match kt?, vt? with
    | some k, some v => return ⟨.lit (.arr []), .map k v⟩
    | _, _ => eerr p "the type of an empty map{} must be given (e.g. M:[string]int = map{})"
  | (k0, v0) :: _ =>
    let rk0 ← elabE ctx k0 kt?
    let rv0 ← elabE ctx v0 vt?
    let kt := kt?.getD rk0.ty
    let vt := vt?.getD rv0.ty
    let mut steps : Array Expr := #[]
    let mut slots : Array (Nat × Nat) := #[]
    for (k, v) in entries do
      let rk ← elabE ctx k (some kt)
      let rv ← elabE ctx v (some vt)
      let tk ← fresh kt
      let tv ← fresh vt
      steps := steps.push (.assign tk (← coerce k.pos rk kt))
      steps := steps.push (.assign tv (← coerce v.pos rv vt))
      slots := slots.push (tk, tv)
    let n := slots.size
    let items := (List.range n).map fun i =>
      let (tk, tv) := slots[i]!
      let later := ((List.range n).filter (· > i)).map fun j => Expr.prim .ne [.local tk, .local slots[j]!.1]
      let cond := later.foldr Expr.seq (.lit (.logic true))
      Expr.ite cond (.prim .mkArr [.prim .mkTup [.local tk, .local tv]]) (.lit (.arr []))
    let built := Expr.prim .flatten [.prim .mkArr items]
    return ⟨steps.toList.foldr Expr.seq built, .map kt vt⟩

partial def elabCase (ctx : Ctx) (p : Pos) (scrut : SExpr) (arms : List (Option SExpr × SExpr))
    (exp : Option Ty) : EM R := do
  let rs ← elabE ctx scrut none
  match rs.ty with
  | .int | .logic | .char | .arr .char | .enum _ => pure ()
  | t => eerr p s!"case works on int, logic, char, string and enums, not {t.show}"
  let t ← fresh rs.ty
  let elabArms : List (Option SExpr × SExpr) → EM (Expr × Ty) := fun arms => do
    let mut results : Array (Option Expr × R) := #[]
    for (pat, v) in arms do
      let rv ← elabE ctx v exp
      match pat with
      | none => results := results.push (none, rv)
      | some pe =>
        let rp ← elabE ctx pe (some rs.ty)
        if rp.ty != rs.ty then eerr pe.pos s!"pattern of type {rp.ty.show} for a {rs.ty.show}"
        results := results.push (some rp.e, rv)
    let mut ty : Ty := .never
    for (_, rv) in results do ty ← join p ty rv.ty exp
    let hasDefault := results.any (·.1.isNone)
    -- an enum case that names every enumerator needs no `_` (Book of Verse §7.6)
    let exhaustive := match rs.ty with
      | .enum n =>
        let k := ((ctx.types.enums.lookup n).getD []).length
        (List.range k).all fun i => results.any fun (pat, _) => match pat with
          | some (.lit (.int j)) => j == i
          | _ => false
      | _ => false
    let mut acc : Expr ← if hasDefault then pure (.lit .void) else
      if exhaustive then pure (.prim .userErr [])   -- unreachable
      else if ctx.canFail then pure (.prim .fail [])
      else eerr p "a case without _ is only allowed where failure is (e.g. a <decides> function), or on an enum when every value is named"
    for (pat, rv) in results.reverse do
      let v ← coerce p rv ty
      match pat with
      | none => acc := v
      | some pe => acc := .ite (p2 .eq (.local t) pe) v acc
    return (acc, ty)
  let (body, ty) ← elabArms arms
  return ⟨.seq (.assign t rs.e) body, ty⟩
end

/-- An elaborated program and the certificate under which it type-checks:
    `prog.check`, `prog.checkTypes sigs slotTys` and `prog.checkControl` hold,
    so `Prog.accepted` applies to it. -/
structure Compiled where
  prog    : Prog
  sigs    : Sigs
  slotTys : List (List VTy)

/-- Elaborate a parsed program into a Verse Core program that passes `Prog.check`
    and `Prog.checkTypes`. -/
def elabProgram (allTops : List STop) : Except String Compiled := do
  -- the type definitions: `name := struct …` and `name := enum …`
  let isTypeDef : STop → Bool
    | .const _ _ none (.structDef ..) | .const _ _ none (.enumDef ..) => true
    | _ => false
  let tops := allTops.filter (!isTypeDef ·)
  let mut env : TyEnv := {}
  for t in allTops do
    match t with
    | .const _ n none (.enumDef _ vals) => env := { env with enums := env.enums ++ [(n, vals)] }
    | .const _ n none (.structDef _ _) => env := { env with structs := env.structs ++ [(n, [])] }
    | _ => pure ()
  let shell := env
  let mut structs := #[]
  for t in allTops do
    match t with
    | .const p n none (.structDef _ fs) =>
      let fields ← fs.mapM fun (f, sty, d, _) => do
        let (ty, _) ← (resolveTy shell p sty).run {}
        pure (f, ty, d)
      structs := structs.push (n, fields)
    | _ => pure ()
  env := { env with structs := structs.toList }
  if let some n := env.recursiveStruct? then
    throw s!"struct {n} contains itself (recursive struct types are not supported)"
  let names := tops.map fun | .fn _ n .. => n | .const _ n .. => n
  for (n, i) in names.zip (List.range names.length) do
    if names.take i |>.contains n then throw s!"'{n}' is defined twice (openverse v1 has no overloading)"
    if builtins.contains n then throw s!"'{n}' is a built-in function"
  -- signatures: functions from their annotations, constants from theirs or by inference
  let mut sigs : Array Sig := #[]
  for (top, idx) in tops.zip (List.range tops.length) do
    match top with
    | .fn p n ps effs ret _ =>
      if effs.contains "suspends" then throw s!"{p.show}: <suspends> (concurrency) is not supported by openverse v1"
      let (tys, _) ← ((ps.mapM fun prm => resolveTy env p prm.ty).run {})
      let (rt, _) ← (resolveTy env p ret).run {}
      -- named parameters come last (Book of Verse §8.2)
      let rec namedLast : List SParam → Bool
        | [] => true
        | q :: qs => if q.named then qs.all (·.named) else namedLast qs
      if !namedLast ps then throw s!"{p.show}: in {n}, every parameter after a named one must be named"
      sigs := sigs.push { idx, name := n, params := tys, ret := rt, decides := effs.contains "decides",
                          isConst := false,
                          named := (ps.filter (·.named)).map fun q => (q.name, q.default) }
    | .const p n sty _ =>
      let rt ← match sty with
        | some t => do let (rt, _) ← (resolveTy env p t).run {}; pure rt
        | none => pure .never   -- inferred below
      sigs := sigs.push { idx, name := n, params := [], ret := rt, decides := false, isConst := true }
  let mkSigProg (sigs : Array Sig) : Prog :=
    { fns := sigs.toList.map fun s =>
        { name := s.name, arity := s.params.length, nslots := 0, decides := s.decides, body := .lit .void },
      main := 0 }
  -- infer the types of unannotated constants, in order
  for (top, idx) in tops.zip (List.range tops.length) do
    match top with
    | .const p n none body =>
      let ctx : Ctx := { sigs := sigs.toList, sigProg := mkSigProg sigs, types := env }
      let (r, _) ← (elabE ctx body none).run {}
      if r.ty == .never then throw s!"{p.show}: cannot infer the type of '{n}'"
      sigs := sigs.set! idx { sigs[idx]! with ret := r.ty }
    | _ => pure ()
  let sigProg := mkSigProg sigs
  let mut fns : Array Fn := #[]
  let mut slotTys : Array (List VTy) := #[]
  for (top, idx) in tops.zip (List.range tops.length) do
    let sig := sigs[idx]!
    match top with
    | .fn p n ps _ _ body =>
      let locals := (ps.zip (List.range ps.length)).zip sig.params |>.map fun ((prm, i), t) =>
        ({ name := prm.name, slot := i, ty := t, mutable := false } : Local)
      for (prm, i) in ps.zip (List.range ps.length) do
        if ps.take i |>.any (·.name == prm.name) then throw s!"{p.show}: duplicate parameter '{prm.name}'"
      let ctx : Ctx := { sigs := sigs.toList, sigProg, locals := locals.reverse, types := env,
                         canFail := sig.decides, retTy := sig.ret }
      let ((r, _), st) ← (elabStmt ctx body (some sig.ret)).run
        { nslots := ps.length, slotTys := sig.params.toArray }
      let (e, _) ← (coerce p r sig.ret).run st
      let e := if sig.ret == .void then Expr.seq e (.lit .void) else e
      let tys := st.slotTys.toList.map (Ty.toVTy env)
      -- every non-parameter slot starts with the default of its type (OpenVerse.Core.Typing)
      let e := initPrefix ps.length (tys.drop ps.length) e
      fns := fns.push { name := n, arity := ps.length, nslots := st.nslots, decides := sig.decides, body := e }
      slotTys := slotTys.push tys
    | .const p n _ body =>
      let ctx : Ctx := { sigs := sigs.toList, sigProg, types := env }
      let (r, st) ← (elabStmt ctx body (some sig.ret)).run {}
      let (e, _) ← (coerce p r.1 sig.ret).run st
      let tys := st.slotTys.toList.map (Ty.toVTy env)
      fns := fns.push { name := n, arity := 0, nslots := st.nslots, decides := false,
                        body := initPrefix 0 tys e }
      slotTys := slotTys.push tys
  let main ← match sigs.toList.find? (·.name == "Main") with
    | some s =>
      if s.isConst || !s.params.isEmpty then throw "Main must be a function with no parameters"
      pure s.idx
    | none => throw "the program has no Main() function"
  let P : Prog := { fns := fns.toList, main }
  if !P.check then throw "internal error: the elaborated program does not pass Prog.check"
  if !P.checkControl then throw "internal error: the elaborated program does not pass Prog.checkControl"
  let S : Sigs := sigs.toList.map fun s => (s.params.map (Ty.toVTy env), s.ret.toVTy env)
  if !P.checkTypes S slotTys.toList then
    throw "internal error: the elaborated program does not pass Prog.checkTypes"
  return { prog := P, sigs := S, slotTys := slotTys.toList }

/-- Parse and elaborate Verse source text. -/
def compileChecked (src : String) : Except String Compiled := do
  elabProgram (← parseProgram src)

/-- Parse and elaborate Verse source text. -/
def compile (src : String) : Except String Prog := do
  return (← compileChecked src).prog

end OpenVerse.Front
