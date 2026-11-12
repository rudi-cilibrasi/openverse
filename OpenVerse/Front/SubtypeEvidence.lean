/- Checked dictionary plans for source upper bounds (#502). No Core cast is
   introduced: a dictionary's Up method is checked at its ordinary input and
   result types. Plans keep lexical names, never slots from another frame. -/
import OpenVerse.Front.Types

namespace OpenVerse.Front.SubtypeEvidence

structure Bound where
  base : Ty
  derived : Ty
  deriving Repr, Inhabited

instance : BEq Bound := ⟨fun a b => a.base == b.base && a.derived == b.derived⟩

def Bound.subst (bound : Bound) (σ : List (String × Ty)) : Bound :=
  { base := bound.base.subst σ, derived := bound.derived.subst σ }

def Bound.ty (bound : Bound) : Ty := .struct family [bound.base, bound.derived]

/-- Bounds on reference classes are carried by private readonly dictionaries.
    Value structs keep their existing equality representation. Inherited
    fields are substituted by the ordinary class-field layout pass. -/
def addFields (tops : List STop) : List STop := tops.map fun
  | .classDef p owner params specs parents iface fields overrides methods =>
    let proofs := params.filterMap fun parameter => do
      let base ← parameter.upperBound
      let name := fieldName owner parameter.name
      if fields.any (·.1 == name) then none else
        let ty := STy.app family [base, .name parameter.name]
        some (name, ty, some (.app p (.ident p "$subtypeWitness")
          [.construct p family [base, .name parameter.name] []] false), false)
    .classDef p owner params specs parents iface (fields ++ proofs) overrides methods
  | top => top

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
    .classDef p rationalFamily [] ["computes"] [dict (.name "rational") (.name "int")] false [] []
      [.fn p "Up" [{ name := "$input", ty := .name "int" }] [] ["override", "computes"]
        (.name "rational") (.ident p "$input")],
    .classDef p eraseFamily [tp "$subtypeC"] ["computes"] [dict (.name "any") c] false [] []
      [.fn p "Up" [input] [] ["override", "computes"] (.name "any") (.ident p "$input")],
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
  let sourceBounds := (env.sbounds.lookup source).getD []
  let covered := params.filterMap fun (name, comparable) =>
    sourceBounds.find? fun (_, derived) => derived == .param name comparable
  let tps := params.map fun (name, comparable) =>
    match sourceBounds.find? (fun (_, derived) => derived == .param name comparable) with
    | some (base, _) => TParam.withUpperBound p name base.toSTy
    | none => ({ pos := p, name, constraint := if comparable then "comparable" else "type" } : TParam)
  let owner := nominalFamily source target
  let extra := (sourceBounds.filter (!covered.contains ·)).map fun (base, derived) =>
    (base.toSTy, derived.toSTy)
  return .classDef p owner tps ["computes"]
    [(.struct family [base, derived] : Ty).toSTy] false (relationFields p owner extra) []
    [.fn p "Up" [{ name := "$input", ty := derived.toSTy }] [] ["override", "computes"]
      base.toSTy (.ident p "$input")]

def declarationName : STop → String
  | .fn _ name .. | .classDef _ name .. | .const _ name .. => name

def mergeRequests (old added : List STop) : List STop :=
  added.foldl (fun result declaration =>
    if result.any (fun old => declarationName old == declarationName declaration) then result
    else result ++ [declaration]) old

inductive Plan where
  | identity : Ty → Plan
  | rational
  | erase : Ty → Plan
  | nominal : (source target : String) → (args : List Ty) → Plan
  | local : String → Bound → Plan
  | field : (receiver field : String) → Bound → Plan
  | compose : Plan → Plan → Plan
  deriving Repr, Inhabited

def Plan.bound (env : TyEnv) : Plan → Bound
  | .identity t => ⟨t, t⟩
  | .rational => ⟨.rational, .int⟩
  | .erase t => ⟨.any, t⟩
  | .nominal source target args =>
    ⟨.struct target (env.upArgs source args target), .struct source args⟩
  | .local _ bound => bound
  | .field _ _ bound => bound
  | .compose outer inner => ⟨(outer.bound env).base, (inner.bound env).derived⟩

private def fieldBound? (env : TyEnv) (ty : Ty) (field : String) : Option Bound := do
  let .struct owner args := ty | none
  if !env.isRefClass owner || !field.startsWith fieldPrefix || env.isVarField owner field then none else do
    let (_, fieldTy, _) ← (env.fields owner args).find? (·.1 == field)
    boundOf? fieldTy

/-- Only current lexical values and compiler-owned readonly proof fields
    carry executable evidence. Do not search arbitrary object graphs, mutable
    fields, or the dummy values stored in hidden type-value witness fields. -/
def capabilities (env : TyEnv) (locals : List (String × Ty)) : List Plan :=
  (locals.map (·.1)).eraseDups.flatMap fun name =>
    match locals.lookup name with
    | none => []
    | some ty =>
      ((boundOf? ty).map (Plan.local name)).toList ++
      (match ty with
       | .struct owner args => if !env.isRefClass owner then [] else
           (env.fields owner args).filterMap fun (field, fieldTy, _) =>
             if !field.startsWith fieldPrefix || env.isVarField owner field then none
             else (boundOf? fieldTy).map (Plan.field name field)
       | _ => [])

/-- Source declarations must state their constraints. Compiler-owned
    helpers can instead carry them in actual captured dictionary objects. -/
def helperContext (name : String) : Bool :=
  name.startsWith "$" || ["$dispatchDefaults", "$spawnBody", ".$call"].any fun part =>
    (name.splitOn part).length > 1

def parameterFacts (env : TyEnv) (parameters : List (Ty × Bool))
    (allowFields : Bool := false) : List (Ty × Ty) :=
  let actual := parameters.zipIdx.map fun ((ty, typeValue), i) =>
    (s!"$argument{i}", if typeValue then Ty.void else ty)
  if allowFields then (capabilities env actual).map fun plan =>
    let bound := plan.bound env
    (bound.base, bound.derived)
  else actual.filterMap fun (_, ty) =>
    (boundOf? ty).map fun bound => (bound.base, bound.derived)

/-- Only real readonly compiler captures can justify generated environment
    fields. Hidden type-value fields never contribute facts. A user class's
    ordinary object fields cannot invent a missing declaration constraint. -/
def fieldFacts (env : TyEnv) (owner : String)
    (fields : List (String × Ty × Option SExpr)) : List (Ty × Ty) :=
  fields.flatMap fun (name, ty, _) =>
    if env.isVarField owner name || name.startsWith "$w." then []
    else if name.startsWith fieldPrefix then
      (boundOf? ty).toList.map fun bound => (bound.base, bound.derived)
    else if (owner.startsWith "$" || owner.endsWith "$fn") && name.startsWith "$capture" then
      parameterFacts env [(ty, false)] true
    else []

/-- Match constraints to the receiver's own resolved field layout. Caller
    evidence slots never determine a field or a slot in the callee. -/
def fieldsForBounds (env : TyEnv) (receiver : Ty) (bounds : List Bound) : List (Nat × Nat) :=
  match receiver with
  | .struct owner args =>
    if !env.isRefClass owner then [] else
      bounds.zipIdx.filterMap fun (bound, index) => do
        let field ← (env.fields owner args).findIdx? fun (name, ty, _) =>
          name.startsWith fieldPrefix && !env.isVarField owner name && boundOf? ty == some bound
        return (index, field)
  | _ => []

/-- Validate even plans supplied through the compiler API. A stale/cross-frame
    assumption cannot be repaired with a similarly named or typed unrelated
    slot. The caller supplies its current locals by name and resolved type. -/
def Plan.valid (env : TyEnv) (locals : List (String × Ty)) : Plan → Bool
  | .identity _ => true
  | .rational | .erase _ => true
  | .nominal source target args =>
    env.isRefClass source && env.isRefClass target && env.isSub source target &&
      args.length == ((env.sparams.lookup source).getD []).length
  | .local name bound => ((locals.lookup name).bind boundOf?) == some bound
  | .field receiver fieldLabel bound =>
    ((locals.lookup receiver).bind (fieldBound? env · fieldLabel)) == some bound
  | .compose outer inner => outer.valid env locals && inner.valid env locals &&
      (outer.bound env).derived == (inner.bound env).base

private def direct? (env : TyEnv) (base derived : Ty) : Option Plan := do
  if derived == base then return .identity derived
  if base == .any then return .erase derived
  if derived == .int && base == .rational then return .rational
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
  let available := capabilities env locals
  go available (available.length + 1) [] bound.derived
where
  go : List Plan → Nat → List Ty → Ty → Option Plan
    | _, 0, _, _ => none
    | available, fuel + 1, seen, derived => do
      if let some plan := direct? env bound.base derived then return plan
      if seen.contains derived then none else do
        available.findSome? fun capability => do
          let relation := capability.bound env
          let before ← direct? env relation.derived derived
          let outer ← go available fuel (derived :: seen) relation.base
          let inner := if relation.derived == derived then capability
            else .compose capability before
          if relation.base == bound.base then some inner else some (.compose outer inner)

/-- Surface expression with symbolic lexical captures. The elaborator resolves
    each name in the new frame; no caller frame's numeric slot is retained. -/
def Plan.value (env : TyEnv) (p : Pos) : Plan → SExpr
  | .identity t => .construct p identityFamily [t.toSTy] []
  | .rational => .construct p rationalFamily [] []
  | .erase t => .construct p eraseFamily [t.toSTy] []
  | .nominal source target args => .construct p (nominalFamily source target) (args.map Ty.toSTy) []
  | .local name _ => .ident p name
  | .field receiver fieldLabel _ => .member p (.ident p receiver) fieldLabel
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
  | .local .. | .field .. => true
  | .compose outer inner => outer.usesLocal || inner.usesLocal
  | _ => false

/-- Nominal views proved by actual lexical dictionaries. Declaration facts
    alone do not create a view from which executable members may be read. -/
def views (env : TyEnv) (locals : List (String × Ty)) (derived : Ty) : List Ty :=
  ((capabilities env locals).filterMap fun capability => do
    let relation := capability.bound env
    let .struct name _ := relation.base | none
    if !env.classes.contains name then none else do
      let plan ← find? env locals ⟨relation.base, derived⟩
      if plan.usesLocal then some relation.base else none).eraseDups

/-- Collapse equal type identities without strengthening comparable flags
    according to which occurrence happened to be visited first. -/
private def mergeTypes (types : List Ty) : List Ty :=
  types.foldl (fun result ty =>
    if result.any (· == ty) then result.map (fun old => if old == ty then old.commonBounds ty else old)
    else result ++ [ty]) []

private def upperViews (env : TyEnv) (derived : Ty) : List Ty :=
  let known := derived :: env.boundFacts.filterMap fun (upper, _) =>
    if env.boundSubtype derived upper then some upper else none
  let nominal := known ++ known.flatMap fun
    | .struct source args => if env.classes.contains source then
        (env.supers source).map fun target => Ty.struct target (env.upArgs source args target)
      else []
    | _ => []
  mergeTypes (nominal ++ (if nominal.contains .int then [.rational] else []) ++ [.any])

/-- A common upper type supported by the nominal relation. Match ordinary
    joins' preference for a shared class when multiple nominal interfaces
    remain, and refuse unrelated interface ambiguity. Input bindings and
    their precise types are never replaced by this inferred upper type. -/
private def commonUpper? (env : TyEnv) (types : List Ty) : Option Ty := do
  let first ← types.head?
  let candidates := (upperViews env first).filter fun candidate =>
    types.all (env.boundSubtype · candidate)
  let best := candidates.filter fun candidate => !candidates.any fun other =>
    other != candidate && env.boundSubtype other candidate && !env.boundSubtype candidate other
  let selected ← match best with
    | [one] => some one
    | _ =>
      if !best.all (fun | .struct name _ => env.classes.contains name | _ => false) then none else
      match best.filter (fun | .struct name _ => !(env.info name).isIface | _ => false) with
      | [one] => some one
      | _ => none
  -- Type identity ignores comparable flags; a join retains only guarantees
  -- present in every projected occurrence of that same type.
  return (types.flatMap (upperViews env) |>.filter (· == selected)).foldl Ty.commonBounds selected

private def peerInstances (env : TyEnv) (bounds : List Bound) (names : List String)
    (substitution : List (String × Ty)) : Option (List (String × Ty)) := do
  let mut lowerTypes := names.map fun name => (name, (substitution.lookup name).toList)
  -- Propagate actual lower types through peer edges before choosing any
  -- upper. This also solves a cycle reached from a known argument.
  for _ in [0:names.length + 1] do
    let previous := lowerTypes
    for bound in bounds do
      let .param upper _ := bound.base | continue
      let values := if bound.derived.params.all (fun n => (substitution.lookup n).isSome) then
          [bound.derived.subst substitution]
        else match bound.derived with
          | .param lower _ => (lowerTypes.lookup lower).getD []
          | _ => []
      lowerTypes := lowerTypes.map fun (name, old) =>
        (name, if name == upper then mergeTypes (old ++ values) else old)
    if (lowerTypes.zip previous).all (fun ((name, values), (oldName, oldValues)) =>
        name == oldName && values.length == oldValues.length &&
        (values.zip oldValues).all (fun (a, b) => a == b && a.paramsC == b.paramsC)) then break
  -- A compound lower type may depend on another inferred instance. Do not
  -- commit a narrower upper before all its incoming constraints are known.
  let mut pending := bounds.filterMap fun bound => do
    let .param upper _ := bound.base | none
    if bound.derived.params.all (fun n => (substitution.lookup n).isSome) then none else
    match bound.derived with
    | .param lower _ => if ((lowerTypes.lookup lower).getD []).isEmpty then some upper else none
    | _ => some upper
  for _ in [0:names.length + 1] do
    let previous := pending
    for bound in bounds do
      if let (.param upper _, .param lower _) := (bound.base, bound.derived) then
        if (substitution.lookup lower).isNone && pending.contains lower then
          pending := (upper :: pending).eraseDups
    if pending.length == previous.length then break
  let mut result := substitution
  for (name, values) in lowerTypes do
    if (result.lookup name).isSome || pending.contains name || values.isEmpty then continue
    let upper ← commonUpper? env values
    result := (name, upper) :: result
  return result

/-- An expected result can suggest an instance, but cannot force a known
    violation of a declaration bound (for example t := any under vehicle).
    Leave incomplete constraints for argument/default inference. This is a
    static filter; every executable relation still requires a dictionary. -/
def acceptsKnownBounds (env : TyEnv) (bounds : List Bound)
    (substitution : List (String × Ty)) : Bool :=
  bounds.all fun bound =>
    if (bound.base.params ++ bound.derived.params).all (fun name => (substitution.lookup name).isSome) then
      env.boundSubtype (bound.derived.subst substitution) (bound.base.subst substitution)
    else true

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
      | .param .. => pure ()
      | .struct target _ =>
        let candidates := derived :: (env.boundFacts.filterMap fun (upper, _) =>
          if env.boundSubtype derived upper then some upper else none)
        let projected := mergeTypes (candidates.filterMap fun
          | .struct source args =>
            if env.classes.contains source && env.isSub source target then
              some (Ty.struct target (env.upArgs source args target)) else none
          | _ => none)
        if projected.isEmpty then continue
        let solutions ← projected.mapM (bound.base.matchArg env substitution)
        let candidate ← solutions.head?
        -- Multiple incompatible projections have no unique inferred
        -- instance. Declaration order must not choose an arbitrary one.
        if !solutions.all (fun other => names.all fun name =>
            candidate.lookup name == other.lookup name) then none else
          substitution := candidate.map fun (name, ty) =>
            if (substitution.lookup name).isSome then (name, ty) else
              (name, solutions.foldl (fun ty solution => ty.commonBounds ((solution.lookup name).getD ty)) ty)
      | _ => pure ()
    if peerTypes then substitution ← peerInstances env bounds names substitution
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
