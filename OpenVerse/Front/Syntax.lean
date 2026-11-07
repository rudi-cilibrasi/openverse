/-
  OpenVerse front end — the surface syntax tree of the supported Verse subset.
-/
namespace OpenVerse.Front

structure Pos where
  line : Nat
  col  : Nat
  /-- The file, for a definition imported from another file (#27). -/
  file : String := ""
  deriving Repr, Inhabited

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
  deriving Repr, Inhabited

/-- A type parameter from a `where` clause (`t:type` or
    `t:subtype(comparable)`), or of a parametric struct `name(t:type) := struct`. -/
structure TParam where
  pos  : Pos
  name : String
  /-- The constraint as written: `type`, or the argument of `subtype(…)`. -/
  constraint : String
  deriving Repr, Inhabited

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
  | structDef : Pos → List TParam → List (String × STy × Option SExpr × Bool) → SExpr
  /-- `enum:` (closed) or `enum<open>:`, which may gain values (Book of Verse ch. 9). -/
  | enumDef  : Pos → List String → (isOpen : Bool) → SExpr
  /-- `type{_X:t where c₁, c₂, …}`: a refinement type (Book of Verse ch. 11):
      the variable, the base type and the conditions. -/
  | refineDef : Pos → String → STy → List SExpr → SExpr
  /-- `Name{F := e, …}` or `name(t₁, …){F := e, …}`: a struct value. -/
  | construct : Pos → String → List STy → List SExpr → SExpr
  /-- `map{k => v, …}`. -/
  | mapLit   : Pos → List (SExpr × SExpr) → SExpr
  deriving Repr, Inhabited
inductive SPart where
  | text : String → SPart
  | code : SExpr → SPart
  deriving Repr, Inhabited
end

def SExpr.pos : SExpr → Pos
  | .int p _ | .char p _ | .char32 p _ | .float p _ | .str p _ | .ident p _ | .app p _ _ _ | .member p _ _
  | .query p _ | .neg p _ | .notE p _ | .bin p _ _ _ | .cmp p _ _ | .andE p _ _
  | .orE p _ _ | .range p _ _ | .tuple p _ | .block p _ | .arrayLit p _
  | .optionLit p _ | .logicLit p _ | .ite p _ _ _ | .forE p _ _ | .gen p _ _ _
  | .loop p _ | .brk p | .ret p _ | .caseE p _ _ | .decl p _ _ _ _ | .set p _ _ _
  | .structDef p _ _ | .enumDef p _ _ | .refineDef p _ _ _ | .construct p _ _ _ | .mapLit p _ => p

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

/-- Substitute type names: a parent's type parameters by the type arguments
    a subclass gives it (#39). -/
partial def STy.substNames (σ : List (String × STy)) : STy → STy
  | .name n => (σ.lookup n).getD (.name n)
  | .arr t => .arr (t.substNames σ)
  | .opt t => .opt (t.substNames σ)
  | .tup ts => .tup (ts.map (STy.substNames σ))
  | .map k v => .map (k.substNames σ) (v.substNames σ)
  | .app n ts => .app n (ts.map (STy.substNames σ))

end OpenVerse.Front
