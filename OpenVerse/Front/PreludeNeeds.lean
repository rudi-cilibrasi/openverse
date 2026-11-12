import OpenVerse.Front.Syntax

namespace OpenVerse.Front.PreludeNeeds

/-- Public soft-library types supplied by the concurrency helpers. -/
def names : List String := ["event", "sticky_event", "task", "subscribable_event", "cancelable"]

private def relevant (n : String) : Bool :=
  names.contains n || n == "$subev0" || names.any (fun p => n == "$" ++ p)

private def nominal (bound : List String) (n : String) : List String :=
  if relevant n && !bound.contains n then [n] else []

/-- A parameter's spelling is not a nominal dependency. -/
partial def ty (bound : List String) : STy → List String
  | .name n => nominal bound n
  | .app n ts => nominal bound n ++ ts.flatMap (ty bound)
  | .arr t | .opt t => ty bound t
  | .tup ts => ts.flatMap (ty bound)
  | .map k v => ty bound k ++ ty bound v
  | .fn ps es r => (if es.contains "suspends" then ["$suspends"] else []) ++
      ps.flatMap (ty bound) ++ ty bound r

private def binds : SExpr → List String
  | .decl _ n _ _ _ => if n.startsWith "?" then [] else [n]
  | .gen _ n i _ => n :: i.toList
  | .app _ (.ident _ "$defaults") (.block _ ds :: _) false =>
    ds.filterMap fun | .decl _ n _ _ _ => some n | _ => none
  | _ => []

/-- Values and types have separate lexical environments. Only a free cast
    callee is a nominal use; an ordinary callback with that spelling is not. -/
partial def expr (types values : List String) (e : SExpr) : List String :=
  let seq (es : List SExpr) := es.foldl (fun (vs, ns) e =>
    (binds e ++ vs, ns ++ expr types vs e)) (values, [])
  match e with
  | .block _ es => (seq es).2
  | .ite _ cs t e =>
    let (vs, ns) := seq cs
    ns ++ expr types vs t ++ e.toList.flatMap (expr types values)
  | .forE _ cs b =>
    let (vs, ns) := seq cs
    ns ++ expr types vs b
  | .structDef _ tps _ fs =>
    let types := tps.map (·.name) ++ types
    fs.flatMap fun (_, t, d, _) => ty types t ++ d.toList.flatMap (expr types [])
  | .refineDef _ n t cs => ty types t ++ cs.flatMap (expr types (n :: values))
  | _ =>
    let here := match e with
      | .decl _ _ t _ _ => t.toList.flatMap (ty types)
      | .construct _ n ts _ => nominal types n ++ ts.flatMap (ty types)
      | .app _ (.ident _ n) _ _ =>
        if ["$spawn", "$sync", "$race", "$rush", "$branch"].contains n then ["$suspends"]
        else if !values.contains n then nominal types n else []
      | _ => []
    here ++ e.children.flatMap (expr types values)

partial def top (members : List (String × List String)) (types values : List String) : STop → List String
  | .fn _ _ ps tps es r b =>
    let types := tps.map (·.name) ++ types
    let (_, defaults) := ps.foldl (fun (vs, ns) p =>
      (p.name :: vs, ns ++ ty types p.ty ++ p.default.toList.flatMap (expr types vs))) (values, [])
    (if es.contains "suspends" then ["$suspends"] else []) ++ ty types r ++ defaults ++
      expr types (ps.map (·.name) ++ values) b
  | .const _ _ t e => t.toList.flatMap (ty types) ++ expr types values e
  | .classDef _ n tps _ parents _ fs _ ms =>
    let types := tps.map (·.name) ++ types
    let values := ((members.lookup n).getD []) ++ values
    parents.flatMap (ty types) ++
      fs.flatMap (fun (_, t, d, _) => ty types t ++ d.toList.flatMap (expr types [])) ++
      ms.flatMap (top members types values)

/-- Implicit method/field lookup includes inherited source members. Qualified
    module identities have already been resolved before this analysis. -/
def uses (tops : List STop) : List String := Id.run do
  let classes := tops.filterMap fun
    | .classDef _ n _ _ ps _ fs _ ms => some (n,
      ps.filterMap (fun | .name q | .app q _ => some q | _ => none),
      fs.map (·.1) ++ ms.filterMap (fun | .fn _ m .. => some m | _ => none))
    | _ => none
  let mut members := classes.map fun (n, _, own) => (n, own)
  for _ in [0:classes.length + 1] do
    let next := classes.map fun (n, ps, own) =>
      (n, (own ++ ps.flatMap (fun p => (members.lookup p).getD [])).eraseDups)
    if next == members then break
    members := next
  return tops.flatMap (top members [] [])

/-- Undemanded library names are private too: loading task must not reserve
    event against an unrelated generic parameter. Source-owned names always
    retain their source identity, while helper dependencies use the private one. -/
def privateNames (owned used : List String) : List String :=
  names.filter fun n => owned.contains n || !used.contains n

end OpenVerse.Front.PreludeNeeds
