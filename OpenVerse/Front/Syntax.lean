/-
  OpenVerse front end — the surface syntax tree of the supported Verse subset.
-/
import Std.Data.HashSet

namespace OpenVerse.Front

structure Pos where
  line : Nat
  col  : Nat
  /-- The file, for a definition imported from another file (#27). -/
  file : String := ""
  deriving Repr, Inhabited, BEq

def Pos.show (p : Pos) : String :=
  if p.file.isEmpty then s!"{p.line}:{p.col}" else s!"{p.file}:{p.line}:{p.col}"

/-- Surface types. -/
inductive STy where
  /-- `int`, `logic`, `char`, `string`, `void` -/
  | name : String → STy
  /-- `[]t` -/
  | arr  : STy → STy
  /-- `?t` -/
  | opt  : STy → STy
  /-- `tuple(t₁, …)` -/
  | tup  : List STy → STy
  /-- `[k]v` -/
  | map  : STy → STy → STy
  /-- `name(t₁, …)`: a parametric struct applied to type arguments. -/
  | app  : String → List STy → STy
  /-- `type{_(:t₁, …)<effects>:r}` or `t₁->r`: a function type (#210), its
      parameter types, effect specifiers and result type. -/
  | fn   : List STy → List String → STy → STy
  deriving Repr, Inhabited, BEq

/-- Fold over written type names in source order, including application
    heads (`box` in `box(t)`) and function parameter and result types. -/
partial def STy.foldNames (f : α → String → α) (init : α) : STy → α
  | .name n => f init n
  | .arr t | .opt t => t.foldNames f init
  | .tup ts => ts.foldl (STy.foldNames f) init
  | .app n ts => ts.foldl (STy.foldNames f) (f init n)
  | .map k v => v.foldNames f (k.foldNames f init)
  | .fn ps _ r => r.foldNames f (ps.foldl (STy.foldNames f) init)

/-- All written type names, in source order, retaining repetitions. -/
def STy.allNames (t : STy) : List String :=
  (t.foldNames (fun names n => n :: names) []).reverse

/-- Written type names in order of first occurrence. Each name is visited
    once; the set tracks duplicates without depending on its iteration order. -/
def STy.names (t : STy) : List String :=
  let (_, names) := t.foldNames (fun (seen, names) n =>
    if seen.contains n then (seen, names) else (seen.insert n, n :: names))
    (({} : Std.HashSet String), ([] : List String))
  names.reverse

/-- Whether a type mentions `n` as a plain type name, including inside
    function types. Application heads are excluded: `box(t)` mentions `t`. -/
partial def STy.mentions (t : STy) (n : String) : Bool := match t with
  | .name m => m == n
  | .arr u | .opt u => u.mentions n
  | .tup ts | .app _ ts => ts.any (·.mentions n)
  | .map a b => a.mentions n || b.mentions n
  | .fn ps _ r => ps.any (·.mentions n) || r.mentions n

/-- Whether a type mentions any of `vs` as plain type names, with the same
    treatment of application heads as `mentions`. -/
partial def STy.mentionsAny (vs : List String) : STy → Bool
  | .name n => vs.contains n
  | .arr t | .opt t => STy.mentionsAny vs t
  | .tup ts | .app _ ts => ts.any (STy.mentionsAny vs)
  | .map k v => STy.mentionsAny vs k || STy.mentionsAny vs v
  | .fn ps _ r => ps.any (STy.mentionsAny vs) || STy.mentionsAny vs r

/-- A type parameter from a `where` clause (`t:type` or
    `t:subtype(comparable)`), or of a parametric struct `name(t:type) := struct`. -/
structure TParam where
  pos  : Pos
  name : String
  /-- The constraint as written: `type`, or the argument of `subtype(…)`. -/
  constraint : String
  deriving Repr, Inhabited, BEq

mutual
inductive SExpr where
  | int      : Pos → Int → SExpr
  | char     : Pos → Nat → SExpr
  /-- A `0u` char32 literal. -/
  | char32   : Pos → Nat → SExpr
  /-- A float literal (#127): its canonical bits. -/
  | float    : Pos → UInt64 → SExpr
  | str      : Pos → List SPart → SExpr
  | ident    : Pos → String → SExpr
  /-- `e(args)` (`bracket = false`) or `e[args]` (`bracket = true`). -/
  | app      : Pos → SExpr → List SExpr → Bool → SExpr
  | member   : Pos → SExpr → String → SExpr
  | query    : Pos → SExpr → SExpr
  | neg      : Pos → SExpr → SExpr
  | notE     : Pos → SExpr → SExpr
  /-- `+ - * /` -/
  | bin      : Pos → String → SExpr → SExpr → SExpr
  /-- A comparison chain `a op₁ b op₂ c …`. -/
  | cmp      : Pos → SExpr → List (String × SExpr) → SExpr
  | andE     : Pos → SExpr → SExpr → SExpr
  | orE      : Pos → SExpr → SExpr → SExpr
  | range    : Pos → SExpr → SExpr → SExpr
  | tuple    : Pos → List SExpr → SExpr
  /-- A block: a sequence that opens a scope; its value is the last element. -/
  | block    : Pos → List SExpr → SExpr
  | arrayLit : Pos → List SExpr → SExpr
  | optionLit : Pos → SExpr → SExpr
  | logicLit : Pos → SExpr → SExpr
  /-- `if (conds) then t else e` (conditions in order). -/
  | ite      : Pos → List SExpr → SExpr → Option SExpr → SExpr
  /-- `for (clauses) body`. -/
  | forE     : Pos → List SExpr → SExpr → SExpr
  /-- A generator clause `X : src` or `I -> X : src` (only inside `for`). -/
  | gen      : Pos → String → Option String → SExpr → SExpr
  | loop     : Pos → SExpr → SExpr
  | brk      : Pos → SExpr
  | ret      : Pos → Option SExpr → SExpr
  /-- `case (e): p => v …`; `none` is the pattern `_`. -/
  | caseE    : Pos → SExpr → List (Option SExpr × SExpr) → SExpr
  /-- `X:t = e`, `X := e` (`isVar = false`) or `var X:t = e`. -/
  | decl     : Pos → String → Option STy → Bool → SExpr → SExpr
  /-- `set lhs = e` or `set lhs op= e`. -/
  | set      : Pos → SExpr → Option String → SExpr → SExpr
  /-- `struct: fields` — each field: name, type, default value, `var`; the
      type parameters of a parametric struct `name(t:type) := struct: …`. -/
  | structDef : Pos → List TParam → List String → List (String × STy × Option SExpr × Bool) → SExpr
  /-- `enum:` (closed) or `enum<open>:`, which may gain values (Book of Verse ch. 9). -/
  | enumDef  : Pos → List String → (isOpen : Bool) → SExpr
  /-- `type{_X:t where c₁, c₂, …}`: a refinement type (Book of Verse ch. 11):
      the variable, the base type and the conditions. -/
  | refineDef : Pos → String → STy → List SExpr → SExpr
  /-- `Name{F := e, …}` or `name(t₁, …){F := e, …}`: a struct value. -/
  | construct : Pos → String → List STy → List SExpr → SExpr
  /-- `map{k => v, …}`. -/
  | mapLit   : Pos → List (SExpr × SExpr) → SExpr
  deriving Repr, Inhabited, BEq
inductive SPart where
  | text : String → SPart
  | code : SExpr → SPart
  deriving Repr, Inhabited, BEq
end

def SExpr.pos : SExpr → Pos
  | .int p _ | .char p _ | .char32 p _ | .float p _ | .str p _ | .ident p _ | .app p _ _ _ | .member p _ _
  | .query p _ | .neg p _ | .notE p _ | .bin p _ _ _ | .cmp p _ _ | .andE p _ _
  | .orE p _ _ | .range p _ _ | .tuple p _ | .block p _ | .arrayLit p _
  | .optionLit p _ | .logicLit p _ | .ite p _ _ _ | .forE p _ _ | .gen p _ _ _
  | .loop p _ | .brk p | .ret p _ | .caseE p _ _ | .decl p _ _ _ _ | .set p _ _ _
  | .structDef p _ _ _ | .enumDef p _ _ | .refineDef p _ _ _ | .construct p _ _ _ | .mapLit p _ => p

/-- Immediate expression children, in source order, including call heads,
    construction field bindings and case patterns. Type definitions are
    leaves: analyses of their field defaults or refinement conditions must
    handle those explicitly. Constructions may evaluate their fields in a
    different order. -/
def SExpr.children : SExpr → List SExpr
  | .str _ ps => ps.filterMap fun | .code c => some c | _ => none
  | .app _ g as _ => g :: as
  | .member _ x _ | .query _ x | .neg _ x | .notE _ x | .optionLit _ x | .logicLit _ x | .loop _ x
  | .gen _ _ _ x | .decl _ _ _ _ x => [x]
  | .bin _ _ a b | .andE _ a b | .orE _ a b | .range _ a b | .set _ a _ b => [a, b]
  | .cmp _ a r => a :: r.map (·.2)
  | .tuple _ es | .block _ es | .arrayLit _ es | .construct _ _ _ es => es
  | .ite _ cs t e => cs ++ [t] ++ e.toList
  | .forE _ cs b => cs ++ [b]
  | .ret _ x => x.toList
  | .caseE _ sc arms => sc :: arms.flatMap fun (pt, v) => pt.toList ++ [v]
  | .mapLit _ kvs => kvs.flatMap fun (k, v) => [k, v]
  | .int .. | .char .. | .char32 .. | .float .. | .ident .. | .brk ..
  | .structDef .. | .enumDef .. | .refineDef .. => []

/-- `e` with `f` applied to each of its immediate children, the ones
    `children` lists, in that order; everything else is kept. -/
def SExpr.mapChildrenM [Monad m] (f : SExpr → m SExpr) (e : SExpr) : m SExpr :=
  match e with
  | .str p ps => return .str p (← ps.mapM fun | .code c => do return .code (← f c) | t => pure t)
  | .app p g as b => return .app p (← f g) (← as.mapM f) b
  | .member p x m => return .member p (← f x) m
  | .query p x => return .query p (← f x)
  | .neg p x => return .neg p (← f x)
  | .notE p x => return .notE p (← f x)
  | .optionLit p x => return .optionLit p (← f x)
  | .logicLit p x => return .logicLit p (← f x)
  | .loop p x => return .loop p (← f x)
  | .gen p x i src => return .gen p x i (← f src)
  | .decl p n t v x => return .decl p n t v (← f x)
  | .bin p o a b => return .bin p o (← f a) (← f b)
  | .andE p a b => return .andE p (← f a) (← f b)
  | .orE p a b => return .orE p (← f a) (← f b)
  | .range p a b => return .range p (← f a) (← f b)
  | .set p l o r => return .set p (← f l) o (← f r)
  | .cmp p a r => return .cmp p (← f a) (← r.mapM fun (o, b) => do return (o, ← f b))
  | .tuple p es => return .tuple p (← es.mapM f)
  | .block p es => return .block p (← es.mapM f)
  | .arrayLit p es => return .arrayLit p (← es.mapM f)
  | .construct p n ts es => return .construct p n ts (← es.mapM f)
  | .ite p cs t u => return .ite p (← cs.mapM f) (← f t) (← u.mapM f)
  | .forE p cs b => return .forE p (← cs.mapM f) (← f b)
  | .ret p x => return .ret p (← x.mapM f)
  | .caseE p sc arms => return .caseE p (← f sc) (← arms.mapM fun (pt, v) => do return (← pt.mapM f, ← f v))
  | .mapLit p kvs => return .mapLit p (← kvs.mapM fun (k, v) => do return (← f k, ← f v))
  | .int .. | .char .. | .char32 .. | .float .. | .ident .. | .brk ..
  | .structDef .. | .enumDef .. | .refineDef .. => return e

/-- `e` with its children (`children`) replaced by `cs`, in order. -/
def SExpr.withChildren (e : SExpr) (cs : List SExpr) : SExpr :=
  let next (c : SExpr) : StateM (List SExpr) SExpr := modifyGet fun
    | c' :: rest => (c', rest)
    | [] => (c, [])
  (e.mapChildrenM next).run' cs

structure SParam where
  name : String
  ty   : STy
  /-- `?Name:t`: passed by name, as `?Name := e`. -/
  named : Bool := false
  /-- `?Name:t = e`: the value when the call omits it. -/
  default : Option SExpr := none
  deriving Repr, Inhabited

/-- A top-level definition. A function's type parameters are those of its
    `where` clause (`F(X:t where t:type):t`); a function with any is generic. -/
inductive STop where
  | fn    : Pos → String → List SParam → List TParam → List String → STy → SExpr → STop
  | const : Pos → String → Option STy → SExpr → STop
  /-- `name(t:type, …) := class<specs>(parents): fields and methods`, or
      `name := interface(parents): methods`. Each method is an `fn`; an
      abstract one (no body) has the effect `$abstract`. `overrides` are the
      fields declared `Name<override>:t = e`, which give an inherited field a
      new default. A parent is a type: `base(t)` for a parametric one (#39). -/
  | classDef : Pos → String → List TParam → (specs : List String) → (parents : List STy) →
      (isInterface : Bool) → (fields : List (String × STy × Option SExpr × Bool)) →
      (overrides : List String) → (methods : List STop) → STop
  deriving Repr, Inhabited

/-- Type aliases mentioned as bare names; applications keep declaration heads. -/
partial def STy.bareNames : STy → List String
  | .name n => [n]
  | .arr t | .opt t => t.bareNames
  | .tup ts | .app _ ts => ts.flatMap STy.bareNames
  | .map k v => k.bareNames ++ v.bareNames
  | .fn ps _ r => ps.flatMap STy.bareNames ++ r.bareNames

/-- Substitute type names: a parent's type parameters by the type arguments
    a subclass gives it (#39). -/
partial def STy.substNames (σ : List (String × STy)) : STy → STy
  | .name n => (σ.lookup n).getD (.name n)
  -- The typed method prefix records this value's static result as an alias.
  -- Materialize it when a lifted body's type substitution carries that alias.
  | .app "$methodResult" [.name receiver] =>
    (σ.lookup receiver).getD (.app "$methodResult" [.name receiver])
  | .arr t => .arr (t.substNames σ)
  | .opt t => .opt (t.substNames σ)
  | .tup ts => .tup (ts.map (STy.substNames σ))
  | .map k v => .map (k.substNames σ) (v.substNames σ)
  | .app n ts => .app n (ts.map (STy.substNames σ))
  | .fn ps es r => .fn (ps.map (STy.substNames σ)) es (r.substNames σ)

end OpenVerse.Front
