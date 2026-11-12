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

def Plan.usesLocal : Plan → Bool
  | .local .. => true
  | .compose outer inner => outer.usesLocal || inner.usesLocal
  | _ => false

/-- Nominal views proved by actual lexical dictionaries. Declaration facts
    alone do not create a view from which executable members may be read. -/
def views (env : TyEnv) (locals : List (String × Ty)) (derived : Ty) : List Ty :=
  (locals.filterMap fun (_, ty) => do
    let relation ← boundOf? ty
    let .struct name _ := relation.base | none
    if !env.classes.contains name then none else do
      let plan ← find? env locals ⟨relation.base, derived⟩
      if plan.usesLocal then some relation.base else none).eraseDups

/-- Infer parameters which occur only inside a nominal upper bound from the
    argument's projected ancestor. Existing input bindings remain fixed. No
    unrelated interface is guessed to be an ancestor of an opaque parameter. -/
def infer (env : TyEnv) (bounds : List Bound) (initial : List (String × Ty))
    (peerTypes : Bool := false) : Option (List (String × Ty)) := do
  if bounds.isEmpty then return initial
  let mut substitution := initial
  let names := (bounds.flatMap fun bound => bound.base.params ++ bound.derived.params).eraseDups
  for _ in [0:names.length + 1] do
    let previous := substitution
    for bound in bounds do
      if bound.derived.params.any (fun name => (substitution.lookup name).isNone) then continue
      if bound.base.params.all (fun name => (substitution.lookup name).isSome) then continue
      let derived := bound.derived.subst substitution
      match bound.base with
      | .param name _ =>
        if peerTypes && (substitution.lookup name).isNone then
          substitution := (name, derived) :: substitution
      | .struct target _ =>
        let candidates := derived :: (env.boundFacts.filterMap fun (upper, _) =>
          if env.boundSubtype derived upper then some upper else none)
        let projected := (candidates.filterMap fun
          | .struct source args =>
            if env.classes.contains source && env.isSub source target then
              some (Ty.struct target (env.upArgs source args target)) else none
          | _ => none).eraseDups
        if projected.isEmpty then continue
        let solutions ← projected.mapM (bound.base.matchArg env substitution)
        let candidate ← solutions.head?
        -- Multiple incompatible projections have no unique inferred
        -- instance. Declaration order must not choose an arbitrary one.
        if !solutions.all (fun other => names.all fun name =>
            candidate.lookup name == other.lookup name) then none else
          substitution := candidate
      | _ => pure ()
    if substitution == previous then break
  return substitution

/-- Physical frame layout shared by checking, call emission and body
    elaboration. Evidence arguments precede all type-value witnesses, so the
    latter keep a contiguous range even when some come from the receiver.
    Receiver evidence follows that range and is initialized from fields. -/
structure Frame where
  explicit : List Ty
  params : List (String × Bool)
  selfParams : List String := []
  bounds : List Bound := []
  /-- Constraint index and the receiver field holding its dictionary. -/
  selfBounds : List (Nat × Nat) := []

def Frame.callBounds (frame : Frame) : List (Nat × Bound) :=
  frame.bounds.zipIdx.filterMap fun (bound, index) =>
    if (frame.selfBounds.lookup index).isSome then none else some (index, bound)

def Frame.receiverBounds (frame : Frame) : List (Nat × Bound × Nat) :=
  frame.bounds.zipIdx.filterMap fun (bound, index) =>
    (frame.selfBounds.lookup index).map fun field => (index, bound, field)

def Frame.orderedParams (frame : Frame) : List (String × Bool) :=
  frame.params.filter (fun (name, _) => !frame.selfParams.contains name) ++
    frame.params.filter (fun (name, _) => frame.selfParams.contains name)

def Frame.witnessBase (frame : Frame) : Nat := frame.explicit.length + frame.callBounds.length

def Frame.hiddenTypes (frame : Frame) : List Ty :=
  frame.callBounds.map (fun (_, bound) => bound.ty) ++
    frame.orderedParams.map (fun (name, comparable) => Ty.param name comparable) ++
    frame.receiverBounds.map (fun (_, bound, _) => bound.ty)

def Frame.arity (frame : Frame) : Nat :=
  frame.witnessBase + (frame.params.filter fun (name, _) => !frame.selfParams.contains name).length

def Frame.argumentTypes (frame : Frame) : List Ty :=
  (frame.explicit ++ frame.hiddenTypes).take frame.arity

/-- Constraint indices retain their identity when fields supply a subset.
    A generated helper can capture these typed lexical values independently
    of its own frame's hidden argument ordering. -/
def Frame.evidence (frame : Frame) : List (Nat × Bound × Nat) :=
  frame.callBounds.zipIdx.map (fun ((index, bound), i) =>
    (index, bound, frame.explicit.length + i)) ++
  frame.receiverBounds.zipIdx.map (fun ((index, bound, _), i) =>
    (index, bound, frame.witnessBase + frame.params.length + i))

def Frame.receiverFields (frame : Frame) : List Nat := frame.receiverBounds.map (·.2.2)

def Frame.valid (frame : Frame) : Bool :=
  (frame.params.map (·.1)).eraseDups.length == frame.params.length &&
    frame.selfParams.eraseDups.length == frame.selfParams.length &&
    frame.selfParams.all (fun name => frame.params.any (·.1 == name)) &&
    (frame.selfBounds.map (·.1)).eraseDups.length == frame.selfBounds.length &&
    frame.selfBounds.all (fun (index, _) => index < frame.bounds.length)

end OpenVerse.Front.SubtypeEvidence
