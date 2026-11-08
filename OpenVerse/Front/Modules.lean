/-
  OpenVerse front end — modules (#112, Book of Verse ch. 16).

  The parser flattens `name := module:` into definitions of qualified names
  (`A::B::F`) and leaves markers: `$module:A::B`, `$public:A::B::F` and
  `$open:A::|M` (a `using{M}` written in module `A`). This pass rewrites
  every reference to a module member to its qualified name, before
  elaboration, which then sees an ordinary flat program:

  - a bare name resolves from the definition's module outward (its own
    members, then the enclosing modules'), then among the public members of
    the modules opened with `using{…}` in scope (two of them giving the name
    is ambiguous), then as a global;
  - `M.F` and `A.B.F` (and the type `M.c`) name a member of the module `M`,
    found from the scope outward; it must be `<public>` unless the use is
    inside that module (the default is `<internal>`).

  Verse forbids shadowing, so a local may not have a name a resolution
  would rewrite (a member of the module or of an open one): that is refused
  here (elaboration's own check sees only the flat names).
-/
import OpenVerse.Front.Syntax
import Std.Data.HashSet

namespace OpenVerse.Front

/-- A qualified name's parts: `A::B::F` is `[A, B, F]`. -/
def qualParts (n : String) : List String := n.splitOn "::"

def qualJoin (ps : List String) : String := "::".intercalate ps

partial def STy.mapNamesM (f : String → Except String String) : STy → Except String STy
  | .name n => return .name (← f n)
  | .arr t => return .arr (← t.mapNamesM f)
  | .opt t => return .opt (← t.mapNamesM f)
  | .tup ts => return .tup (← ts.mapM (·.mapNamesM f))
  | .map a b => return .map (← a.mapNamesM f) (← b.mapNamesM f)
  | .app n ts => return .app (← f n) (← ts.mapM (·.mapNamesM f))
  | .fn ps es r => return .fn (← ps.mapM (·.mapNamesM f)) es (← r.mapNamesM f)

/-- The names an expression `A.B.C` is a chain of. -/
partial def SExpr.identPath : SExpr → Option (List String)
  | .ident _ n => some [n]
  | .member _ e m => (e.identPath).map (· ++ [m])
  | _ => none

/-- How the names of one scope resolve: values, binders (refused when they
    would shadow a member), type names and paths `A.B.F`. -/
structure Resolver where
  val  : Pos → String → Except String String
  bind : Pos → String → Except String Unit
  ty   : Pos → String → Except String String
  qual : Pos → List String → Except String (Option String)

/-- A method name: `(i:)M`'s interface `i` (or `M.i`) resolved as a type. -/
def Resolver.method (r : Resolver) (p : Pos) (m : String) : Except String String := do
  if m.startsWith "(" then
    if let [q, x] := (m.drop 1).toString.splitOn ":)" then return s!"({← r.ty p q}:){x}"
  return m

/-- Rewrite the names of an expression (see `Resolver`). -/
partial def SExpr.mapNamesM (r : Resolver) : SExpr → Except String SExpr := fun e =>
  let go := SExpr.mapNamesM r
  let goT (p : Pos) := STy.mapNamesM (r.ty p)
  -- (a construction's `Field := v`: a field's name, not a binder)
  let goField : SExpr → Except String SExpr := fun
    | .decl p n ty v x => do return .decl p n (← ty.mapM (goT p)) v (← go x)
    | a => go a
  match e with
  | .int .. | .char .. | .char32 .. | .float .. | .brk _ => return e
  | .str p parts => return .str p (← parts.mapM fun | .text s => pure (.text s) | .code c => do return .code (← go c))
  | .ident p n => do
    -- (`D<constructor>(…)`, a delegation: `D` or `M.D`)
    if n.startsWith "$ctor:" then
      let d := (n.drop "$ctor:".length).toString
      if d.contains '.' then
        match ← r.qual p (d.splitOn ".") with
        | some qd => return .ident p s!"$ctor:{qd}"
        | none => throw s!"{p.show}: unknown constructor {d}"
      return .ident p s!"$ctor:{← r.val p d}"
    return .ident p (← r.val p n)
  | .app p g args b => return .app p (← go g) (← args.mapM go) b
  | .member p x m => do
    -- `(M:)F`, parsed as `Self.(M:)F`: when `M` is a module, its member `F`
    -- (#145), as `M.F`; else a qualified member of `Self`
    if let .ident _ "Self" := x then
      if m.startsWith "(" then
        if let [q, f] := (m.drop 1).toString.splitOn ":)" then
          if let some qn ← r.qual p (q.splitOn "." ++ [f]) then return .ident p qn
    if let some comps := x.identPath then
      if let some qn ← r.qual p (comps ++ [m]) then return .ident p qn
    return .member p (← go x) (← r.method p m)
  | .query p x => return .query p (← go x)
  | .neg p x => return .neg p (← go x)
  | .notE p x => return .notE p (← go x)
  | .bin p o a b => return .bin p o (← go a) (← go b)
  | .cmp p a rest => return .cmp p (← go a) (← rest.mapM fun (o, b) => do return (o, ← go b))
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
  | .gen p x k s => do
    r.bind p x
    if let some k := k then r.bind p k
    return .gen p x k (← go s)
  | .loop p b => return .loop p (← go b)
  | .ret p x => return .ret p (← x.mapM go)
  | .caseE p s arms => return .caseE p (← go s) (← arms.mapM fun (pat, v) => do return (← pat.mapM go, ← go v))
  | .decl p n ty v x => do
    if !n.startsWith "?" then r.bind p n
    return .decl p n (← ty.mapM (goT p)) v (← go x)
  | .set p l o rhs => return .set p (← go l) o (← go rhs)
  | .structDef p tps fs =>
    return .structDef p tps (← fs.mapM fun (n, t, d, v) => do return (n, ← goT p t, ← d.mapM go, v))
  | .enumDef .. | .refineDef .. => return e
  | .construct p n ts fs => return .construct p (← r.ty p n) (← ts.mapM (goT p)) (← fs.mapM goField)
  | .mapLit p kvs => return .mapLit p (← kvs.mapM fun (k, v) => do return (← go k, ← go v))

/-- Resolve the modules of a parsed program (see the file's header). -/
def resolveModules (tops : List STop) : Except String (List STop) := do
  let markers (pre : String) : List (Pos × String) := tops.filterMap fun
    | .const p n _ _ => if n.startsWith pre then some (p, (n.drop pre.length).toString) else none
    | _ => none
  let isMarker (n : String) := n.startsWith "$module:" || n.startsWith "$public:" || n.startsWith "$open:"
  let real := tops.filter fun
    | .const _ n _ _ => !isMarker n
    | _ => true
  let modules := (markers "$module:").map (·.2)
  if modules.isEmpty && (markers "$open:").isEmpty then return real
  let publics := (markers "$public:").map (·.2)
  let defs : List String := real.map fun
    | .fn _ n .. | .const _ n .. | .classDef _ n .. => n
  let defsS : Std.HashSet String := Std.HashSet.ofList defs
  let modsS : Std.HashSet String := Std.HashSet.ofList modules
  let pubS : Std.HashSet String := Std.HashSet.ofList publics
  let shown (n : String) : String := ".".intercalate (qualParts n)
  let shownP (ps : List String) : String := ".".intercalate ps
  let mut seenM : Std.HashSet String := {}
  for (p, m) in markers "$module:" do
    if defsS.contains m then throw s!"{p.show}: {shown m} is defined twice (a module and a definition)"
    if seenM.contains m then throw s!"{p.show}: module {shown m} is defined twice"
    seenM := seenM.insert m
  -- (one name's overloads share their visibility)
  for (p, n) in markers "$public:" do
    if n.contains ':' && (defs.filter (· == n)).length != (publics.filter (· == n)).length && defsS.contains n then
      throw s!"{p.show}: the overloads of {shown n} must all be <public> or all internal"
  let inside (sc m : List String) : Bool := m.length ≤ sc.length && sc.take m.length == m
  -- the definition or module a name gives from scope `sc`, the innermost
  -- (`true`: a module)
  let lookup (sc : List String) (n : String) : Option (Bool × List String) := Id.run do
    for k in (List.range (sc.length + 1)).reverse do
      let cand := sc.take k ++ [n]
      if defsS.contains (qualJoin cand) then return some (false, cand)
      if modsS.contains (qualJoin cand) then return some (true, cand)
    return none
  -- each level of `path` after its first `start` parts, used from `sc`, is
  -- visible: public, or used inside its owner
  let checkVis (sc : List String) (p : Pos) (path : List String) (start : Nat) : Except String Unit := do
    for k in [start + 1 : path.length + 1] do
      let lvl := path.take k
      let owner := lvl.dropLast
      if !inside sc owner && !pubS.contains (qualJoin lvl) then
        throw s!"{p.show}: {shownP lvl} is internal to {shownP owner}: mark it <public> to use it outside"
  -- the modules opened, each with the scope it is open in
  let mut opens : List (List String × List String) := []
  for (p, s) in markers "$open:" do
    if let [sc0, path] := s.splitOn "|" then
      let sc := (qualParts sc0).filter (· != "")
      let comps := qualParts path
      let head := comps.headD ""
      -- (the head: a module in scope, or a public submodule of a module
      -- opened before, in scope)
      let viaOpen : Option (List String) := opens.findSome? fun (osc, m) =>
        if inside sc osc && modsS.contains (qualJoin (m ++ [head])) &&
            (pubS.contains (qualJoin (m ++ [head])) || inside sc m) then some (m ++ [head]) else none
      let base ← match lookup sc head, viaOpen with
        | some (true, b), _ => pure b
        | none, some b => pure b
        | _, _ => throw s!"{p.show}: unknown module {shown path}"
      let mut cur := base
      for c in comps.drop 1 do
        if !modsS.contains (qualJoin (cur ++ [c])) then throw s!"{p.show}: unknown module {shown path}"
        cur := cur ++ [c]
      checkVis sc p cur base.length
      opens := opens ++ [(sc, cur)]
  -- the definition or module a name gives from scope `sc`: at each level,
  -- innermost first, the level's own definitions, then the members of the
  -- modules opened there (two of them giving it: ambiguous) (`true`: a module)
  let find (sc : List String) (p : Pos) (n : String) : Except String (Option (Bool × List String)) := do
    for k in (List.range (sc.length + 1)).reverse do
      let pre := sc.take k
      let cand := pre ++ [n]
      if defsS.contains (qualJoin cand) then return some (false, cand)
      if modsS.contains (qualJoin cand) then return some (true, cand)
      let here : List (Bool × List String) := ((opens.filter (·.1 == pre)).filterMap fun (_, m) =>
        let c := m ++ [n]
        let q := qualJoin c
        if !(pubS.contains q || inside sc m) then none
        else if defsS.contains q then some (false, c)
        else if modsS.contains q then some (true, c)
        else none).eraseDups
      match here with
      | [x] => return some x
      | (_, a) :: (_, b) :: _ => throw s!"{p.show}: '{n}' is ambiguous: both {shownP a} and {shownP b} are open"
      | [] => pure ()
    return none
  let resolve (what : String) (sc : List String) (p : Pos) (n : String) : Except String String := do
    match ← find sc p n with
    | some (true, cand) => throw s!"{p.show}: {shownP cand} is a module, not a {what}"
    | some (false, cand) => return qualJoin cand
    | none => return n
  -- a binder: refused if it would shadow a module, or a member of a module
  -- (the top level's names are the elaborator's to check)
  let bind (sc : List String) (p : Pos) (n : String) : Except String Unit := do
    let hit : Option (List String) := match ← find sc p n with
      | some (true, cand) => some cand
      | some (false, cand) => if cand.length > 1 then some cand else none
      | none => none
    if let some cand := hit then
      throw s!"{p.show}: '{n}' is already defined (as {shownP cand}); Verse does not allow shadowing"
  -- a path (module parts, then a member), from scope `sc`
  let qual (sc : List String) (p : Pos) (comps : List String) : Except String (Option String) := do
    match comps with
    | head :: rest@(_ :: _) =>
      -- (a value's name: `X.F` is its field)
      let some (true, base) ← find sc p head | return none
      let mut path := base
      for c in rest.dropLast do
        -- (`M.v.F`: the field `F` of the member `M.v`, resolved as a prefix)
        if !modsS.contains (qualJoin (path ++ [c])) then return none
        path := path ++ [c]
      let last := rest.getLast!
      let qn := path ++ [last]
      if !defsS.contains (qualJoin qn) then
        if modsS.contains (qualJoin qn) then throw s!"{p.show}: module {shownP qn} is not a value"
        throw s!"{p.show}: module {shownP path} has no member {last}"
      checkVis sc p qn base.length
      return some (qualJoin qn)
    | _ => return none
  let tyName (sc excl : List String) (p : Pos) (n : String) : Except String String := do
    if excl.contains n then return n
    if n.contains '.' then
      match ← qual sc p (n.splitOn ".") with
      | some qn => return qn
      | none => throw s!"{p.show}: unknown type '{n}'"
    resolve "type" sc p n
  let scopeOf (n : String) : List String := (qualParts n).dropLast
  let rAt (sc excl : List String) : Resolver :=
    { val := resolve "value" sc, bind := bind sc, ty := tyName sc excl, qual := qual sc }
  -- each class's members, its own and inherited (a method body sees them
  -- bare, so none may be named like a visible member)
  let classInfo : List (String × List String × List String) ← real.filterMapM fun
    | .classDef p n tps _ parents _ fields _ methods => do
      let r := rAt (scopeOf n) (tps.map (·.name))
      let ps ← parents.mapM fun t => do
        match ← t.mapNamesM (r.ty p) with
        | .name q | .app q _ => pure q
        | _ => pure ""
      let own := fields.map (·.1) ++ methods.filterMap fun
        | .fn _ mn .. => if mn.startsWith "(" || mn.startsWith "$" then none else some mn
        | _ => none
      return some (n, ps, own)
    | _ => return none
  let budget := 1 + classInfo.foldl (fun a (_, ps, _) => a + ps.length + 1) 0
  let membersOf (c : String) : List String := Id.run do
    let mut seen : List String := []
    let mut todo := [c]
    let mut out : List String := []
    for _ in [0:budget] do
      match todo with
      | [] => break
      | x :: rest =>
        todo := rest
        if !seen.contains x then
          seen := x :: seen
          if let some (_, ps, own) := classInfo.find? (·.1 == x) then
            out := out ++ own
            todo := todo ++ ps
    return out.eraseDups
  let params (r : Resolver) (p : Pos) (ps : List SParam) : Except String (List SParam) := do
    for prm in ps do r.bind p prm.name
    ps.mapM fun prm => do
      return { prm with ty := ← prm.ty.mapNamesM (r.ty p), default := ← prm.default.mapM (·.mapNamesM r) }
  real.mapM fun t => do
    match t with
    | .fn p n ps tps effs ret body =>
      let r := rAt (scopeOf n) (tps.map (·.name))
      let ps ← params r p ps
      let isCtor := effs.any (·.startsWith "$constructor:")
      let effs ← effs.mapM fun e =>
        if e.startsWith "$constructor:" then do return s!"$constructor:{← r.ty p (e.drop "$constructor:".length).toString}"
        else pure e
      -- (a constructor's `F := e` items initialise fields: not binders)
      let body ← match isCtor, body with
        | true, .block bp items => do
          let items ← items.mapM fun
            | .decl dp dn ty v x => do return .decl dp dn (← ty.mapM (·.mapNamesM (r.ty dp))) v (← x.mapNamesM r)
            | it => it.mapNamesM r
          pure (SExpr.block bp items)
        | _, _ => body.mapNamesM r
      return .fn p n ps tps effs (← ret.mapNamesM (r.ty p)) body
    | .const p n ty body =>
      let r := rAt (scopeOf n) []
      return .const p n (← ty.mapM (·.mapNamesM (r.ty p))) (← body.mapNamesM r)
    | .classDef p n tps specs parents isI fields ovs methods =>
      let r := rAt (scopeOf n) (tps.map (·.name))
      for m in membersOf n do r.bind p m
      let parents ← parents.mapM (·.mapNamesM (r.ty p))
      let fields ← fields.mapM fun (fn, ty, d, v) => do return (fn, ← ty.mapNamesM (r.ty p), ← d.mapM (·.mapNamesM r), v)
      let methods ← methods.mapM fun m => do
        match m with
        | .fn mp mn mps mtps meffs mret mbody =>
          let rm := rAt (scopeOf n) (tps.map (·.name) ++ mtps.map (·.name))
          let mps ← params rm mp mps
          return .fn mp (← rm.method mp mn) mps mtps meffs (← mret.mapNamesM (rm.ty mp)) (← mbody.mapNamesM rm)
        | m => pure m
      return .classDef p n tps specs parents isI fields ovs methods

end OpenVerse.Front
