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

/-- The names an expression `A.B.C` is a chain of. -/
partial def SExpr.identPath : SExpr → Option (List String)
  | .ident _ n => some [n]
  | .member _ e m => (e.identPath).map (· ++ [m])
  | _ => none

/-- Rewrite the identifiers (`f`), type names (`ft`) and qualified accesses
    (`q`: the qualified name a path names, if it names a module member). -/
partial def SExpr.mapNamesM (f : Pos → String → Except String String) (ft : String → Except String String)
    (q : Pos → List String → Except String (Option String)) : SExpr → Except String SExpr := fun e =>
  let go := SExpr.mapNamesM f ft q
  let goT := STy.mapNamesM ft
  -- a binder: its name must not be a visible member's
  let bind (p : Pos) (n : String) : Except String Unit := do
    let r ← f p n
    if r != n then
      throw s!"{p.show}: '{n}' is already defined (as {".".intercalate (r.splitOn "::")}); Verse does not allow shadowing"
  -- (a construction's `Field := v`: a field's name, not a binder)
  let goField : SExpr → Except String SExpr := fun
    | .decl p n ty v x => do return .decl p n (← ty.mapM goT) v (← go x)
    | a => go a
  match e with
  | .int .. | .char .. | .char32 .. | .brk _ => return e
  | .str p parts => return .str p (← parts.mapM fun | .text s => pure (.text s) | .code c => do return .code (← go c))
  | .ident p n => return .ident p (← f p n)
  | .app p g args b => return .app p (← go g) (← args.mapM go) b
  | .member p x m => do
    if let some comps := x.identPath then
      if let some qn ← q p (comps ++ [m]) then return .ident p qn
    return .member p (← go x) m
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
    bind p x
    if let some k := k then bind p k
    return .gen p x k (← go s)
  | .loop p b => return .loop p (← go b)
  | .ret p x => return .ret p (← x.mapM go)
  | .caseE p s arms => return .caseE p (← go s) (← arms.mapM fun (pat, v) => do return (← pat.mapM go, ← go v))
  | .decl p n ty v x => do
    if !n.startsWith "?" then bind p n
    return .decl p n (← ty.mapM goT) v (← go x)
  | .set p l o r => return .set p (← go l) o (← go r)
  | .structDef p tps fs =>
    return .structDef p tps (← fs.mapM fun (n, t, d, v) => do return (n, ← goT t, ← d.mapM go, v))
  | .enumDef .. => return e
  | .construct p n ts fs => return .construct p (← ft n) (← ts.mapM goT) (← fs.mapM goField)
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
  for (p, m) in markers "$module:" do
    if defs.contains m then
      throw s!"{p.show}: {".".intercalate (qualParts m)} is defined twice (a module and a definition)"
    if (modules.filter (· == m)).length > 1 then
      throw s!"{p.show}: module {".".intercalate (qualParts m)} is defined twice"
  -- a module named from scope `sc` (its parts), innermost first
  let findModule (sc : List String) (path : List String) : Option (List String) :=
    ((List.range (sc.length + 1)).reverse.map fun k => sc.take k ++ path).find? fun m =>
      modules.contains (qualJoin m)
  let shown (n : String) : String := ".".intercalate (qualParts n)
  -- the modules opened, each with the scope it is open in
  let opens : List (List String × List String) ← (markers "$open:").filterMapM fun (p, s) => do
    match s.splitOn "|" with
    | [sc, path] =>
      let scParts := (qualParts sc).filter (· != "")
      match findModule scParts (qualParts path) with
      | some m => return some (scParts, m)
      | none => throw s!"{p.show}: unknown module {shown path}"
    | _ => return none
  let inside (sc m : List String) : Bool := m.length ≤ sc.length && sc.take m.length == m
  -- a path (module parts, then a member), from scope `sc`
  let qualified (sc : List String) (p : Pos) (comps : List String) : Except String (Option String) := do
    match comps with
    | head :: rest@(_ :: _) =>
      -- (the head: a module from the scope outward, else a public submodule
      -- of a module opened in scope)
      let viaOpen : Option (List String) := (opens.filter fun (osc, _) => inside sc osc).findSome? fun (_, m) =>
        if modules.contains (qualJoin (m ++ [head])) && publics.contains (qualJoin (m ++ [head])) then
          some (m ++ [head]) else none
      let some base := (findModule sc [head]).orElse fun _ => viaOpen | return none
      let path := base ++ rest.dropLast
      if !modules.contains (qualJoin path) then return none
      let qn := qualJoin (path ++ [rest.getLast!])
      if !defs.contains qn then
        if modules.contains qn then throw s!"{p.show}: module {shown qn} is not a value"
        throw s!"{p.show}: module {shown (qualJoin path)} has no member {rest.getLast!}"
      -- (each level used from outside it is public: the member, and the
      -- submodules on the way)
      for k in [base.length + 1 : path.length + 2] do
        let lvl := (path ++ [rest.getLast!]).take k
        let owner := lvl.dropLast
        if !inside sc owner && !publics.contains (qualJoin lvl) then
          throw s!"{p.show}: {shown (qualJoin lvl)} is internal to {shown (qualJoin owner)}: mark it <public> to use it outside"
      return some qn
    | _ => return none
  -- a bare name, from scope `sc`
  let bare (sc : List String) (p : Pos) (n : String) : Except String String := do
    for k in (List.range sc.length).reverse do
      let qn := qualJoin (sc.take (k + 1) ++ [n])
      if defs.contains qn then return qn
    let opened : List String := (opens.filter fun (osc, _) => inside sc osc).filterMap fun (_, m) =>
      let qn := qualJoin (m ++ [n])
      if defs.contains qn && publics.contains qn then some qn else none
    match opened.eraseDups with
    | [qn] => return qn
    | [] =>
      if (findModule sc [n]).isSome then throw s!"{p.show}: {n} is a module, not a value"
      return n
    | a :: b :: _ => throw s!"{p.show}: '{n}' is ambiguous: both {shown a} and {shown b} are open"
  let typeName (sc : List String) (p : Pos) (n : String) : Except String String := do
    if n.contains '.' then
      match ← qualified sc p (n.splitOn ".") with
      | some qn => return qn
      | none => throw s!"{p.show}: unknown type '{n}'"
    bare sc p n
  let scopeOf (n : String) : List String := (qualParts n).dropLast
  let bindAll (sc : List String) (p : Pos) (ns : List String) : Except String Unit := do
    for n in ns do
      let r ← bare sc p n
      if r != n then
        throw s!"{p.show}: '{n}' is already defined (as {shown r}); Verse does not allow shadowing"
  real.mapM fun t => do
    match t with
    | .fn p n ps tps effs ret body =>
      let sc := scopeOf n
      let f := bare sc
      let ft := typeName sc p
      let q := qualified sc
      bindAll sc p (ps.map (·.name))
      let ps ← ps.mapM fun prm => do
        return { prm with ty := ← prm.ty.mapNamesM ft, default := ← prm.default.mapM (·.mapNamesM f ft q) }
      let effs ← effs.mapM fun e =>
        if e.startsWith "$constructor:" then do return s!"$constructor:{← ft (e.drop "$constructor:".length).toString}"
        else pure e
      return .fn p n ps tps effs (← ret.mapNamesM ft) (← body.mapNamesM f ft q)
    | .const p n ty body =>
      let sc := scopeOf n
      return .const p n (← ty.mapM (·.mapNamesM (typeName sc p))) (← body.mapNamesM (bare sc) (typeName sc p) (qualified sc))
    | .classDef p n tps specs parents isI fields ovs methods =>
      let sc := scopeOf n
      let f := bare sc
      let ft := typeName sc p
      let q := qualified sc
      bindAll sc p (fields.map (·.1))
      bindAll sc p (methods.filterMap fun
        | .fn _ mn .. => if mn.startsWith "(" || mn.startsWith "$" then none else some mn
        | _ => none)
      let parents ← parents.mapM (·.mapNamesM ft)
      let fields ← fields.mapM fun (fn, ty, d, v) => do return (fn, ← ty.mapNamesM ft, ← d.mapM (·.mapNamesM f ft q), v)
      let methods ← methods.mapM fun m => do
        match m with
        | .fn mp mn mps mtps meffs mret mbody =>
          bindAll sc mp (mps.map (·.name))
          let mps ← mps.mapM fun prm => do
            return { prm with ty := ← prm.ty.mapNamesM ft, default := ← prm.default.mapM (·.mapNamesM f ft q) }
          return .fn mp mn mps mtps meffs (← mret.mapNamesM ft) (← mbody.mapNamesM f ft q)
        | m => pure m
      return .classDef p n tps specs parents isI fields ovs methods

end OpenVerse.Front
