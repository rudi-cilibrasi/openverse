/- Checked dictionary plans for source upper bounds (#502). No Core cast is
   introduced: a dictionary's Up method is checked at its ordinary input and
   result types. Plans keep lexical names, never slots from another frame. -/
import OpenVerse.Front.Types

namespace OpenVerse.Front.SubtypeEvidence

def family : String := "$subtypeEvidence"
def identityFamily : String := "$subtypeIdentity"
def composeFamily : String := "$subtypeCompose"

structure Bound where
  base : Ty
  derived : Ty
  deriving Repr, Inhabited

instance : BEq Bound := ⟨fun a b => a.base == b.base && a.derived == b.derived⟩

def Bound.subst (bound : Bound) (σ : List (String × Ty)) : Bound :=
  { base := bound.base.subst σ, derived := bound.derived.subst σ }

def Bound.ty (bound : Bound) : Ty := .struct family [bound.base, bound.derived]

/-- Only an actual dictionary type establishes a relation. In particular, a
    matching lexical name alone carries no evidence. -/
def boundOf? : Ty → Option Bound
  | .struct n [base, derived] => if n == family then some { base, derived } else none
  | _ => none

/-- The protocol is compiler-owned. Source cannot spell its `$` names. Its
    implementations remain ordinary nominal classes checked by the front end
    and by the polymorphic Core checker. -/
def protocol (p : Pos) : List STop := Id.run do
  let tp (name : String) : TParam := { pos := p, name, constraint := "type" }
  let a := STy.name "$subtypeA"
  let b := STy.name "$subtypeB"
  let c := STy.name "$subtypeC"
  let dict (base derived : STy) := STy.app family [base, derived]
  let input : SParam := { name := "$input", ty := c }
  let up (value : SExpr) := SExpr.app p (.member p value "Up") [.ident p "$input"] false
  return [
    .classDef p family [tp "$subtypeA", tp "$subtypeC"] ["computes"] [] true [] []
      [.fn p "Up" [input] [] ["$abstract", "computes"] a (.tuple p [])],
    .classDef p identityFamily [tp "$subtypeC"] ["computes"] [dict c c] false [] []
      [.fn p "Up" [input] [] ["override", "computes"] c (.ident p "$input")],
    .classDef p composeFamily [tp "$subtypeA", tp "$subtypeB", tp "$subtypeC"]
      ["computes"] [dict a c] false
      [("$outer", dict a b, none, false), ("$inner", dict b c, none, false)] []
      [.fn p "Up" [input] [] ["override", "computes"] a
        (.app p (.member p (.ident p "$outer") "Up") [up (.ident p "$inner")] false)]]

def nominalFamily (source target : String) : String :=
  s!"$subtypeNominal{source.length}_{source}{target.length}_{target}"

/-- One family per nominal inheritance edge, at the declaration's parameters,
    rather than a new class at each closed instance. This keeps polymorphic
    recursion finite. All nominal upcasts are still checked in Up's body. -/
def nominal (env : TyEnv) (p : Pos) (source target : String) : Except String STop := do
  unless env.isRefClass source && env.isRefClass target && env.isSub source target do
    throw s!"invalid nominal subtype evidence: {source} is not below {target}"
  let params := (env.sparams.lookup source).getD []
  let own := params.map fun (name, comparable) => Ty.param name comparable
  let derived := Ty.struct source own
  let base := Ty.struct target (env.upArgs source own target)
  let tps := params.map fun (name, comparable) =>
    ({ pos := p, name, constraint := if comparable then "comparable" else "type" } : TParam)
  return .classDef p (nominalFamily source target) tps ["computes"]
    [(.struct family [base, derived] : Ty).toSTy] false [] []
    [.fn p "Up" [{ name := "$input", ty := derived.toSTy }] [] ["override", "computes"]
      base.toSTy (.ident p "$input")]

inductive Plan where
  | identity : Ty → Plan
  | nominal : (source target : String) → (args : List Ty) → Plan
  | local : String → Bound → Plan
  | compose : Plan → Plan → Plan
  deriving Repr, Inhabited

def Plan.bound (env : TyEnv) : Plan → Bound
  | .identity t => ⟨t, t⟩
  | .nominal source target args =>
    ⟨.struct target (env.upArgs source args target), .struct source args⟩
  | .local _ bound => bound
  | .compose outer inner => ⟨(outer.bound env).base, (inner.bound env).derived⟩

/-- Validate even plans supplied through the compiler API. A stale/cross-frame
    assumption cannot be repaired with a similarly named or typed unrelated
    slot. The caller supplies its current locals by name and resolved type. -/
def Plan.valid (env : TyEnv) (locals : List (String × Ty)) : Plan → Bool
  | .identity _ => true
  | .nominal source target args =>
    env.isRefClass source && env.isRefClass target && env.isSub source target &&
      args.length == ((env.sparams.lookup source).getD []).length
  | .local name bound => ((locals.lookup name).bind boundOf?) == some bound
  | .compose outer inner => outer.valid env locals && inner.valid env locals &&
      (outer.bound env).derived == (inner.bound env).base

private def direct? (env : TyEnv) (base derived : Ty) : Option Plan := do
  if derived == base then return .identity derived
  let (.struct source args, .struct target targets) := (derived, base) | none
  if env.isRefClass source && env.isRefClass target && env.isSub source target &&
      args.length == ((env.sparams.lookup source).getD []).length &&
      env.upArgs source args target == targets then
    some (.nominal source target args)
  else none

/-- Derive a plan using exact type relations and nominal ancestry. Unrelated
    interfaces need not be disjoint: absence of a proof here only means this
    context cannot perform this upcast. A visited-type set terminates cycles
    in dependent bounds without discarding an available acyclic path. -/
def find? (env : TyEnv) (locals : List (String × Ty)) (bound : Bound) : Option Plan :=
  go (locals.length + 1) [] bound.derived
where
  go : Nat → List Ty → Ty → Option Plan
    | 0, _, _ => none
    | fuel + 1, seen, derived => do
      if let some plan := direct? env bound.base derived then return plan
      if seen.contains derived then none else do
        locals.findSome? fun (name, ty) => do
          let relation ← boundOf? ty
          let before ← direct? env relation.derived derived
          let outer ← go fuel (derived :: seen) relation.base
          let inner := if relation.derived == derived then Plan.local name relation
            else .compose (.local name relation) before
          if relation.base == bound.base then some inner else some (.compose outer inner)

/-- Surface expression with symbolic lexical captures. The elaborator resolves
    each name in the new frame; no caller frame's numeric slot is retained. -/
def Plan.value (env : TyEnv) (p : Pos) : Plan → SExpr
  | .identity t => .construct p identityFamily [t.toSTy] []
  | .nominal source target args => .construct p (nominalFamily source target) (args.map Ty.toSTy) []
  | .local name _ => .ident p name
  | .compose outer inner =>
    let left := outer.bound env
    let right := inner.bound env
    .construct p composeFamily [left.base.toSTy, left.derived.toSTy, right.derived.toSTy]
      [.decl p "$outer" none false (outer.value env p),
       .decl p "$inner" none false (inner.value env p)]

/-- All canonical nominal families needed by a plan, in stable dependency
    order. Repeated instantiations share their single generic declaration. -/
def Plan.nominals : Plan → List (String × String)
  | .nominal source target _ => [(source, target)]
  | .compose outer inner => (outer.nominals ++ inner.nominals).eraseDups
  | _ => []

end OpenVerse.Front.SubtypeEvidence
