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

/-- Obligations needed to write concrete type applications in a generated
    declaration. Inspect arguments and declared upper heads, not object fields.
    Declaration names bound recursion even for polymorphic recursive heads. -/
partial def applicationBounds (env : TyEnv) (types : List Ty) : List Bound :=
  (types.flatMap (go [])).eraseDups
where
  go (seen : List String) : Ty → List Bound
    | .arr ty | .opt ty => go seen ty
    | .tup tys => tys.flatMap (go seen)
    | .map key value => go seen key ++ go seen value
    | .struct owner args =>
      let nested := args.flatMap (go seen)
      if seen.contains owner then nested else
        let substitution := ((env.sparams.lookup owner).getD []).map (·.1) |>.zip args
        let bounds := ((env.sbounds.lookup owner).getD []).map fun (base, derived) =>
          Bound.mk (base.subst substitution) (derived.subst substitution)
        nested ++ bounds ++ bounds.flatMap (fun bound => go (owner :: seen) bound.base)
    | _ => []

def Bound.subst (bound : Bound) (σ : List (String × Ty)) : Bound :=
  { base := bound.base.subst σ, derived := bound.derived.subst σ }

def Bound.ty (bound : Bound) : Ty := .struct family [bound.base, bound.derived]

/-- Bounds on reference classes are carried by private readonly dictionaries.
    Value structs keep their existing equality representation. Inherited
    fields are substituted by the ordinary class-field layout pass. -/
def addFields (tops : List STop) : List STop := tops.map fun
  | .classDef p owner nsp params specs parents iface fields methods =>
    let proofs := params.filterMap fun parameter => do
      let base ← parameter.upperBound
      let name := fieldName owner parameter.name
      if fields.any (·.name == name) then none else
        let ty := STy.app family [base, .name parameter.name]
        some { name, ty, default := some (.app p (.ident p "$subtypeWitness")
          [.construct p family [base, .name parameter.name] []] false) }
    .classDef p owner nsp params specs parents iface (fields ++ proofs) methods
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
  let ka := STy.name "$subtypeKA"
  let kc := STy.name "$subtypeKC"
  let dict (base derived : STy) := STy.app family [base, derived]
  let input : SParam := { name := "$input", ty := c }
  let up (value : SExpr) := SExpr.app p (.member p value "Up") [.ident p "$input"] false
  let lift (name : String) (params : List TParam) (base derived : STy) : STop :=
    .classDef p name [] params ["computes"] [dict base derived] false
      [{ name := "$element", ty := dict a c }]
      [.fn p "Up" [{ name := "$input", ty := derived }] [] ["override", "computes"] base
        (.app p (.ident p "$subtypeLift") [.ident p "$input", .ident p "$element"] false)]
  return [
    .classDef p family [] [tp "$subtypeA", tp "$subtypeC"] ["computes"] [] true []
      [.fn p "Up" [input] [] ["$abstract", "computes"] a (.tuple p [])],
    .classDef p identityFamily [] [tp "$subtypeC"] ["computes"] [dict c c] false []
      [.fn p "Up" [input] [] ["override", "computes"] c (.ident p "$input")],
    .classDef p rationalFamily [] [] ["computes"] [dict (.name "rational") (.name "int")] false []
      [.fn p "Up" [{ name := "$input", ty := .name "int" }] [] ["override", "computes"]
        (.name "rational") (.ident p "$input")],
    .classDef p eraseFamily [] [tp "$subtypeC"] ["computes"] [dict (.name "any") c] false []
      [.fn p "Up" [input] [] ["override", "computes"] (.name "any") (.ident p "$input")],
    .classDef p discardFamily [] [tp "$subtypeC"] ["computes"] [dict (.name "void") c] false []
      [.fn p "Up" [input] [] ["override", "computes"] (.name "void") (.ident p "$input")],
    .classDef p bottomFamily [] [tp "$subtypeA"] ["computes"] [dict a (.name "$never")] false []
      [.fn p "Up" [{ name := "$input", ty := .name "$never" }] [] ["override", "computes"] a
        (.app p (.ident p "Err") [] false)],
    lift arrayFamily [tp "$subtypeA", tp "$subtypeC"] (.arr a) (.arr c),
    lift optionFamily [tp "$subtypeA", tp "$subtypeC"] (.opt a) (.opt c),
    .classDef p mapFamily []
      [{ pos := p, name := "$subtypeKA", constraint := "comparable" },
       { pos := p, name := "$subtypeKC", constraint := "comparable" }, tp "$subtypeA", tp "$subtypeC"]
      ["computes"] [dict (.map ka a) (.map kc c)] false
      [{ name := "$key", ty := dict ka kc }, { name := "$element", ty := dict a c }]
      [.fn p "Up" [{ name := "$input", ty := .map kc c }] [] ["override", "computes"] (.map ka a)
        (.app p (.ident p "$subtypeLift") [.ident p "$input", .ident p "$key", .ident p "$element"] false)],
    .classDef p composeFamily [] [tp "$subtypeA", tp "$subtypeB", tp "$subtypeC"]
      ["computes"] [dict a c] false
      [{ name := "$outer", ty := dict a b }, { name := "$inner", ty := dict b c }]
      [.fn p "Up" [input] [] ["override", "computes"] a
        (.app p (.member p (.ident p "$outer") "Up") [up (.ident p "$inner")] false)]]

/-- Tuple dictionaries share one generic declaration per arity, including
    when their components contain other tuples or polymorphic instances. -/
def tupleDeclaration (p : Pos) (arity : Nat) : STop :=
  let names := List.range arity
  let bases := names.map fun i => STy.name s!"$tupleA{i}"
  let derived := names.map fun i => STy.name s!"$tupleC{i}"
  let params := (names.map (fun i => s!"$tupleA{i}") ++ names.map (fun i => s!"$tupleC{i}")).map
    fun name => ({ pos := p, name, constraint := "type" } : TParam)
  let fields := (bases.zip derived).zipIdx.map fun ((a, c), i) =>
    ({ name := s!"$element{i}", ty := STy.app family [a, c] } : SField)
  .classDef p (tupleFamily arity) [] params ["computes"]
    [.app family [.tup bases, .tup derived]] false fields
    [.fn p "Up" [{ name := "$input", ty := .tup derived }] [] ["override", "computes"] (.tup bases)
      (.app p (.ident p "$subtypeLift")
        (.ident p "$input" :: names.map (fun i => .ident p s!"$element{i}")) false)]

def tupleArrayDeclaration (p : Pos) (arity : Nat) : Except String STop := do
  if arity == 0 then throw "an empty tuple is void, not a tuple-to-array subtype"
  let names := List.range arity
  let base := STy.name "$tupleA"
  let derived := names.map fun i => STy.name s!"$tupleC{i}"
  let params := ("$tupleA" :: names.map (fun i => s!"$tupleC{i}")).map
    fun name => ({ pos := p, name, constraint := "type" } : TParam)
  let fields := derived.zipIdx.map fun (ty, i) =>
    ({ name := s!"$element{i}", ty := STy.app family [base, ty] } : SField)
  return .classDef p (tupleArrayFamily arity) [] params ["computes"]
    [.app family [.arr base, .tup derived]] false fields
    [.fn p "Up" [{ name := "$input", ty := .tup derived }] [] ["override", "computes"] (.arr base)
      (.app p (.ident p "$subtypeLift")
        (.ident p "$input" :: names.map (fun i => .ident p s!"$element{i}")) false)]

def refinementFamily (source : String) (target : Ty) : String :=
  s!"$subtypeRefinement{source.length}_{source}{target.show.length}_{target.show}"

/-- Refinement widening is checked by the same ordinary conversion as a
    concrete source result. It never uses a literal to invent membership. -/
def refinementDeclaration (env : TyEnv) (p : Pos) (source : String) (target : Ty) : Except String STop := do
  unless env.refinementSubtype source target do throw s!"invalid refinement subtype evidence for {source}"
  return .classDef p (refinementFamily source target) [] [] ["computes"]
    [.app family [target.toSTy, .name source]] false []
    [.fn p "Up" [{ name := "$input", ty := .name source }] [] ["override", "computes"]
      target.toSTy (.ident p "$input")]

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
  return .classDef p owner [] tps ["computes"]
    [(.struct family [base, derived] : Ty).toSTy] false (relationFields p owner extra)
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
  | discard : Ty → Plan
  | bottom : Ty → Plan
  | nominal : (source target : String) → (args : List Ty) → Plan
  | local : String → Bound → Plan
  | field : (receiver field : String) → Bound → Plan
  | compose : Plan → Plan → Plan
  | array : Plan → Plan
  | option : Plan → Plan
  | map : Plan → Plan → Plan
  | tuple : List Plan → Plan
  | tupleArray : Ty → List Plan → Plan
  | refinement : String → Ty → Plan
  deriving Repr, Inhabited

partial def Plan.bound (env : TyEnv) : Plan → Bound
  | .identity t => ⟨t, t⟩
  | .rational => ⟨.rational, .int⟩
  | .erase t => ⟨.any, t⟩
  | .discard t => ⟨.void, t⟩
  | .bottom t => ⟨t, .never⟩
  | .refinement source target => ⟨target, .refine source⟩
  | .nominal source target args =>
    ⟨.struct target (env.upArgs source args target), .struct source args⟩
  | .local _ bound => bound
  | .field _ _ bound => bound
  | .compose outer inner => ⟨(outer.bound env).base, (inner.bound env).derived⟩
  | .array element => ⟨.arr (element.bound env).base, .arr (element.bound env).derived⟩
  | .option element => ⟨.opt (element.bound env).base, .opt (element.bound env).derived⟩
  | .map key element => ⟨.map (key.bound env).base (element.bound env).base,
      .map (key.bound env).derived (element.bound env).derived⟩
  | .tuple elements => ⟨.tup (elements.map fun e => (e.bound env).base),
      .tup (elements.map fun e => (e.bound env).derived)⟩
  | .tupleArray element elements => ⟨.arr element, .tup (elements.map fun e => (e.bound env).derived)⟩

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

/-- Could a formal input expose executable proof or function data? This is a refusal
    check, not evidence search: containers and ordinary fields may forward
    dictionaries even though they do not themselves authorize an upcast.
    Unconstrained parameters remain opaque, so parametric forwarding keeps
    its value's role without being mistaken for proof consumption. -/
partial def exposesEvidence (env : TyEnv) (ty : Ty) : Bool :=
  go [] [] ty
where
  go (owners : List String) (parameters : List String) : Ty → Bool
    | .arr t | .opt t => go owners parameters t
    | .tup ts => ts.any (go owners parameters)
    | .map k v => go owners parameters k || go owners parameters v
    | .param name _ => !parameters.contains name && env.boundFacts.any fun (upper, lower) =>
        lower == .param name false && go owners (name :: parameters) upper
    | .struct name args =>
      name == family || env.isSub name family || (FnValues.parseName name).isSome ||
        args.any (go owners parameters) ||
        (!owners.contains name && (env.fields name args).any fun (field, ty, _) =>
          !field.startsWith "$w." && go (name :: owners) parameters ty)
    | _ => false

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
partial def Plan.valid (env : TyEnv) (locals : List (String × Ty)) : Plan → Bool
  | .identity _ => true
  | .rational | .erase _ | .discard _ | .bottom _ => true
  | .refinement source target => env.refinementSubtype source target
  | .nominal source target args =>
    env.isRefClass source && env.isRefClass target && env.isSub source target &&
      args.length == ((env.sparams.lookup source).getD []).length
  | .local name bound => ((locals.lookup name).bind boundOf?) == some bound
  | .field receiver fieldLabel bound =>
    ((locals.lookup receiver).bind (fieldBound? env · fieldLabel)) == some bound
  | .compose outer inner => outer.valid env locals && inner.valid env locals &&
      (outer.bound env).derived == (inner.bound env).base
  | .array element | .option element => element.valid env locals
  | .map key element => isComparable env (key.bound env).base &&
      isComparable env (key.bound env).derived && key.valid env locals && element.valid env locals
  | .tuple elements => elements.all (·.valid env locals)
  | .tupleArray element elements => !elements.isEmpty && elements.all fun plan =>
      plan.valid env locals && (plan.bound env).base == element

private def direct? (env : TyEnv) (base derived : Ty) : Option Plan := do
  if derived == base then return .identity derived
  if derived == .never then return .bottom base
  if base == .any then return .erase derived
  if base == .void then return .discard derived
  if derived == .int && base == .rational then return .rational
  if let .refine source := derived then
    if env.refinementSubtype source base then return .refinement source base
  let (.struct source args, .struct target targets) := (derived, base) | none
  if env.isRefClass source && env.isRefClass target && env.isSub source target &&
      args.length == ((env.sparams.lookup source).getD []).length &&
      env.upArgs source args target == targets then
    some (.nominal source target args)
  else none

/-- Search whole relations and covariant components without distributing a
    whole-container capability to its elements. Every recursive goal uses
    subterms of the original goal or of a finite capability endpoint; no
    intermediate type is synthesized. Visited pairs terminate cyclic facts
    while allowing nested components to reuse the same real dictionary. -/
partial def find? (env : TyEnv) (locals : List (String × Ty)) (bound : Bound) : Option Plan :=
  let available := capabilities env locals
  go available [] bound
where
  go (available : List Plan) (seen : List Bound) (goal : Bound) : Option Plan := do
    if let some plan := direct? env goal.base goal.derived then return plan
    if seen.contains goal then none else do
      let seen := goal :: seen
      let structural : Option Plan := match goal.base, goal.derived with
        | .arr a, .arr c => (go available seen ⟨a, c⟩).map Plan.array
        | .opt a, .opt c => (go available seen ⟨a, c⟩).map Plan.option
        | .map k a, .map l c =>
          if !isComparable env k || !isComparable env l then none else do
            let key ← go available seen ⟨k, l⟩
            let element ← go available seen ⟨a, c⟩
            return .map key element
        | .tup bases, .tup cs =>
          if bases.length == cs.length then
            ((bases.zip cs).mapM fun (a, c) => go available seen ⟨a, c⟩).map Plan.tuple
          else none
        | .arr a, .tup cs =>
          if cs.isEmpty then none else
            (cs.mapM fun c => go available seen ⟨a, c⟩).map (Plan.tupleArray a)
        | _, _ => none
      if let some plan := structural then return plan
      available.findSome? fun capability => do
        let relation := capability.bound env
        let before ← go available seen ⟨relation.derived, goal.derived⟩
        let after ← go available seen ⟨goal.base, relation.base⟩
        let inner := if relation.derived == goal.derived then capability else .compose capability before
        if relation.base == goal.base then some inner else some (.compose after inner)

/-- Surface expression with symbolic lexical captures. The elaborator resolves
    each name in the new frame; no caller frame's numeric slot is retained. -/
partial def Plan.value (env : TyEnv) (p : Pos) : Plan → SExpr
  | .identity t => .construct p identityFamily [t.toSTy] []
  | .rational => .construct p rationalFamily [] []
  | .erase t => .construct p eraseFamily [t.toSTy] []
  | .discard t => .construct p discardFamily [t.toSTy] []
  | .bottom t => .construct p bottomFamily [t.toSTy] []
  | .refinement source target => .construct p (refinementFamily source target) [] []
  | .nominal source target args => .construct p (nominalFamily source target) (args.map Ty.toSTy) []
  | .local name _ => .ident p name
  | .field receiver fieldLabel _ => .member p (.ident p receiver) fieldLabel
  | .compose outer inner =>
    let left := outer.bound env
    let right := inner.bound env
    .construct p composeFamily [left.base.toSTy, left.derived.toSTy, right.derived.toSTy]
      [.decl p "$outer" none false (outer.value env p),
       .decl p "$inner" none false (inner.value env p)]
  | .array element =>
    let bound := element.bound env
    .construct p arrayFamily [bound.base.toSTy, bound.derived.toSTy]
      [.decl p "$element" none false (element.value env p)]
  | .option element =>
    let bound := element.bound env
    .construct p optionFamily [bound.base.toSTy, bound.derived.toSTy]
      [.decl p "$element" none false (element.value env p)]
  | .map key element =>
    let keys := key.bound env
    let bound := element.bound env
    .construct p mapFamily [keys.base.toSTy, keys.derived.toSTy, bound.base.toSTy, bound.derived.toSTy]
      [.decl p "$key" none false (key.value env p), .decl p "$element" none false (element.value env p)]
  | .tuple elements =>
    let bounds := elements.map (·.bound env)
    .construct p (tupleFamily elements.length)
      (bounds.map (·.base.toSTy) ++ bounds.map (·.derived.toSTy))
      (elements.zipIdx.map fun (element, i) => .decl p s!"$element{i}" none false (element.value env p))
  | .tupleArray element elements =>
    .construct p (tupleArrayFamily elements.length)
      (element.toSTy :: elements.map (fun e => (e.bound env).derived.toSTy))
      (elements.zipIdx.map fun (component, i) => .decl p s!"$element{i}" none false (component.value env p))

/-- All canonical nominal families needed by a plan, in stable dependency
    order. Repeated instantiations share their single generic declaration. -/
partial def Plan.nominals : Plan → List (String × String)
  | .nominal source target _ => [(source, target)]
  | .compose outer inner => (outer.nominals ++ inner.nominals).eraseDups
  | .array element | .option element => element.nominals
  | .map key element => (key.nominals ++ element.nominals).eraseDups
  | .tuple elements | .tupleArray _ elements => (elements.flatMap Plan.nominals).eraseDups
  | _ => []

partial def Plan.tupleArities : Plan → List Nat
  | .tuple elements => (elements.length :: elements.flatMap Plan.tupleArities).eraseDups
  | .tupleArray _ elements => (elements.flatMap Plan.tupleArities).eraseDups
  | .array element | .option element => element.tupleArities
  | .map key element => (key.tupleArities ++ element.tupleArities).eraseDups
  | .compose outer inner => (outer.tupleArities ++ inner.tupleArities).eraseDups
  | _ => []

partial def Plan.tupleArrayArities : Plan → List Nat
  | .tupleArray _ elements => (elements.length :: elements.flatMap Plan.tupleArrayArities).eraseDups
  | .tuple elements => (elements.flatMap Plan.tupleArrayArities).eraseDups
  | .array element | .option element => element.tupleArrayArities
  | .map key element | .compose key element => (key.tupleArrayArities ++ element.tupleArrayArities).eraseDups
  | _ => []

partial def Plan.refinements : Plan → List (String × Ty)
  | .refinement source target => [(source, target)]
  | .tuple elements | .tupleArray _ elements => (elements.flatMap Plan.refinements).eraseDups
  | .array element | .option element => element.refinements
  | .map key element | .compose key element => (key.refinements ++ element.refinements).eraseDups
  | _ => []

partial def Plan.usesLocal : Plan → Bool
  | .local .. | .field .. => true
  | .compose outer inner => outer.usesLocal || inner.usesLocal
  | .array element | .option element => element.usesLocal
  | .map key element => key.usesLocal || element.usesLocal
  | .tuple elements | .tupleArray _ elements => elements.any Plan.usesLocal
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

/-- Whole-value views available from real capabilities, without distributing
    container relations to their elements or using declaration facts alone.
    Equal identities retain only their common comparable guarantees. -/
def valueViews (env : TyEnv) (locals : List (String × Ty)) (derived : Ty) : List Ty :=
  mergeTypes ((capabilities env locals).filterMap fun capability => do
    let relation := capability.bound env
    let plan ← find? env locals ⟨relation.base, derived⟩
    if plan.usesLocal && plan.valid env locals then some relation.base else none)

private def upperViews (env : TyEnv) (derived : Ty) : List Ty :=
  let known := derived :: env.boundFacts.filterMap fun (upper, _) =>
    if env.boundSubtype derived upper then some upper else none
  let known := known ++ known.filterMap fun
    | .refine source => (env.refines.lookup source).bind fun (base, _) =>
        if env.refinementSubtype source base then some base else none
    | _ => none
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
private partial def commonUpper? (env : TyEnv) (types : List Ty)
    (comparable : Bool := false) : Option Ty := do
  let first ← types.head?
  -- Join corresponding components directly, avoiding a Cartesian product
  -- of every upper type of every tuple component.
  let structural : Option Ty := match first with
    | .arr _ => do
      let components ← types.mapM fun | .arr t => some t | _ => none
      return .arr (← commonUpper? env components comparable)
    | .opt _ => do
      let components ← types.mapM fun | .opt t => some t | _ => none
      return .opt (← commonUpper? env components comparable)
    | .map _ _ => do
      let components ← types.mapM fun | .map _ t => some t | _ => none
      let keys ← types.mapM fun | .map k _ => some k | _ => none
      let key ← commonUpper? env keys true
      if !isComparable env key then none else return .map key (← commonUpper? env components comparable)
    | .tup parts => do
      let rows ← types.mapM fun | .tup ts => if ts.length == parts.length then some ts else none | _ => none
      let components ← (List.range parts.length).mapM fun i => do
        commonUpper? env (← rows.mapM (·[i]?)) comparable
      return .tup components
    | _ => none
  let tupleLengths := types.filterMap fun | .tup ts => some ts.length | _ => none
  let needsArray := !tupleLengths.isEmpty &&
    (types.any (fun | .arr _ => true | _ => false) ||
      tupleLengths.any (· != tupleLengths.headD 0))
  -- Matching arrays/tuples already recurse componentwise above. Only a
  -- mixed shape needs this second join; recursing twice at every matching
  -- container depth would make deeply nested inference exponential.
  let tupleArray : Option Ty := if !needsArray then none else do
    let parts ← types.mapM fun | .tup ts => some ts | .arr t => some [t] | _ => none
    let components := parts.flatten
    if components.isEmpty then none else return .arr (← commonUpper? env components comparable)
  let candidates := (mergeTypes (structural.toList ++ tupleArray.toList ++ types.flatMap (upperViews env))).filter fun candidate =>
    (!comparable || isComparable env candidate) && types.all (env.boundSubtype · candidate)
  let best := candidates.filter fun candidate => !candidates.any fun other =>
    other != candidate && env.boundSubtype other candidate && !env.boundSubtype candidate other
  let selected ← match best with
    | [one] => some one
    | _ =>
      let first ← best.head?
      if best.all (fun other => env.boundSubtype first other && env.boundSubtype other first) then
        -- Equivalent upper types (notably any/void and their containers)
        -- have one domain. Pick a stable representative rather than making
        -- argument order choose an instance or reporting false ambiguity.
        some (best.foldl (fun old next => if reprStr next < reprStr old then next else old) first)
      else if !best.all (fun | .struct name _ => env.classes.contains name | _ => false) then none else
      match best.filter (fun | .struct name _ => !(env.info name).isIface | _ => false) with
      | [one] => some one
      | _ => none
  -- Type identity ignores comparable flags; a join retains only guarantees
  -- present in every projected occurrence of that same type.
  return (types.flatMap (upperViews env) |>.filter (· == selected)).foldl Ty.commonBounds selected

/-- A common value view for operations whose ordinary concrete join failed.
    Only actual capabilities contribute opaque relations. At least one input
    must use such a capability, so this does not broaden ordinary joins. -/
def joinView? (env : TyEnv) (locals : List (String × Ty)) (types : List Ty)
    (expected : Option Ty := none) : Option Ty := do
  let facts := (capabilities env locals).map fun capability =>
    let bound := capability.bound env
    (bound.base, bound.derived)
  let actual := { env with boundFacts := facts }
  let candidates := expected.toList ++ (commonUpper? actual types).toList
  candidates.find? fun target =>
    match types.mapM (fun source => find? env locals ⟨target, source⟩) with
    | some plans => plans.any (·.usesLocal) && plans.all (·.valid env locals)
    | none => false

/-- Observe unknown parameters inside a covariant bound head. This proposes
    instances only: it neither distributes a whole-container proof nor adds
    component facts. Calls still prove the complete instantiated relation.
    Distinct views of an opaque input must agree before contributing lowers. -/
private partial def structuralLowers (env : TyEnv) (fixed : List (String × Ty))
    (pattern actual : Ty) : Option (List (String × Ty)) :=
  go [] pattern actual
where
  go (seen : List (Ty × Ty)) (pattern actual : Ty) : Option (List (String × Ty)) := do
    if actual == .never then return []
    if pattern.params.all (fun name => (fixed.lookup name).isSome) then
      if env.boundSubtype actual (pattern.subst fixed) then return [] else none
    match pattern, actual with
    | .param name _, _ =>
      if actual.hasNever then return [] else return [(name, actual)]
    | .arr p, .arr a | .opt p, .opt a => go seen p a
    | .arr p, .tup values => return (← values.mapM (go seen p)).flatten
    | .tup ps, .tup values =>
      if ps.length != values.length then none else
        return (← (ps.zip values).mapM fun (p, a) => go seen p a).flatten
    | .map pk pv, .map ak av => return (← go seen pk ak) ++ (← go seen pv av)
    | .struct .., .struct .. =>
      return (← pattern.matchArg env fixed actual).filter fun (name, _) => (fixed.lookup name).isNone
    | _, _ =>
      if seen.contains (pattern, actual) then none else do
        let results := (upperViews env actual).filterMap fun view =>
          if view == actual then none else go ((pattern, actual) :: seen) pattern view
        let first ← results.head?
        let keys := (first.map (·.1)).eraseDups
        if !results.all (fun result => (result.map (·.1)).eraseDups.length == keys.length &&
            keys.all (fun name => mergeTypes (result.filterMap fun (n, ty) => if n == name then some ty else none) ==
              mergeTypes (first.filterMap fun (n, ty) => if n == name then some ty else none))) then none else
          return first.map fun (name, ty) => (name, results.foldl (fun common result =>
            (result.filterMap fun (n, ty) => if n == name && ty == common then some ty else none).foldl Ty.commonBounds common) ty)

private def peerInstances (env : TyEnv) (bounds : List Bound) (names : List String)
    (substitution : List (String × Ty)) (comparable : List String) : Option (List (String × Ty)) := do
  let mut lowerTypes := names.map fun name => (name, (substitution.lookup name).toList)
  -- Propagate actual lower types through peer edges before choosing any
  -- upper. This also solves a cycle reached from a known argument.
  for _ in [0:names.length + 1] do
    let previous := lowerTypes
    for bound in bounds do
      let values := if bound.derived.params.all (fun n => (substitution.lookup n).isSome) then
          [bound.derived.subst substitution]
        else match bound.derived with
          | .param lower _ => (lowerTypes.lookup lower).getD []
          | _ => []
      match bound.base with
      | .param upper _ =>
        lowerTypes := lowerTypes.map fun (name, old) =>
          (name, if name == upper then mergeTypes (old ++ values) else old)
      | .arr .. | .opt .. | .tup .. | .map .. =>
        for value in values do
          let observations ← structuralLowers env substitution bound.base value
          lowerTypes := lowerTypes.map fun (name, old) =>
            (name, mergeTypes (old ++ observations.filterMap fun (n, ty) => if n == name then some ty else none))
      | _ => pure ()
    if (lowerTypes.zip previous).all (fun ((name, values), (oldName, oldValues)) =>
        name == oldName && values.length == oldValues.length &&
        (values.zip oldValues).all (fun (a, b) => a == b && a.paramsC == b.paramsC)) then break
  -- A compound lower type may depend on another inferred instance. Do not
  -- commit a narrower upper before all its incoming constraints are known.
  let mut pending := bounds.flatMap fun bound =>
    if bound.derived.params.all (fun n => (substitution.lookup n).isSome) then [] else
    match bound.derived with
    | .param lower _ => if ((lowerTypes.lookup lower).getD []).isEmpty then bound.base.params else []
    | _ => bound.base.params
  for _ in [0:names.length + 1] do
    let previous := pending
    for bound in bounds do
      if bound.derived.params.any (fun lower => (substitution.lookup lower).isNone && pending.contains lower) then
        pending := (bound.base.params ++ pending).eraseDups
    if pending.length == previous.length then break
  let mut result := substitution
  for (name, values) in lowerTypes do
    if (result.lookup name).isSome || pending.contains name || values.isEmpty then continue
    let upper ← commonUpper? env values (comparable.contains name)
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

/-- Infer bound-only parameters from nominal projections, structural lower
    observations and peer constraints. Existing input bindings remain fixed.
    No unrelated interface is guessed to be an ancestor of an opaque parameter. -/
def infer (env : TyEnv) (bounds : List Bound) (initial : List (String × Ty))
    (peerTypes : Bool := false) (comparable : List String := []) : Option (List (String × Ty)) := do
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
    if peerTypes then substitution ← peerInstances env bounds names substitution comparable
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
