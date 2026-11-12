import OpenVerse.Front.Syntax

namespace OpenVerse.Front.PreludeNeeds

/-- Public soft-library types supplied by the concurrency helpers. -/
def names : List String := ["event", "sticky_event", "task", "subscribable_event", "cancelable"]

/-- Type applications and nested function types need their definitions even
    in unused declarations. A type parameter with the same spelling does not. -/
partial def ty (bound : List String) : STy → List String
  | .name n => if bound.contains n then [] else [n]
  | .app n ts => (if bound.contains n then [] else [n]) ++ ts.flatMap (ty bound)
  | .arr t | .opt t => ty bound t
  | .tup ts => ts.flatMap (ty bound)
  | .map k v => ty bound k ++ ty bound v
  | .fn ps es r => (if es.contains "suspends" then ["$suspends"] else []) ++
      ps.flatMap (ty bound) ++ ty bound r

/-- Scan types and compiler intrinsics, never coincidental value names or
    string text. Children include interpolation, defaults and constructions. -/
partial def expr (bound : List String) (e : SExpr) : List String :=
  let fields (bound : List String) (fs : List (String × STy × Option SExpr × Bool)) :=
    fs.flatMap fun (_, t, d, _) => ty bound t ++ d.toList.flatMap (expr bound)
  match e with
  | .structDef _ tps _ fs => fields (tps.map (·.name) ++ bound) fs
  | .refineDef _ _ t cs => ty bound t ++ cs.flatMap (expr bound)
  | _ =>
    let here := match e with
      | .decl _ _ t _ _ => t.toList.flatMap (ty bound)
      | .construct _ n ts _ => (if bound.contains n then [] else [n]) ++ ts.flatMap (ty bound)
      | .app _ (.ident _ n) _ _ =>
        if ["$spawn", "$sync", "$race", "$rush", "$branch"].contains n then ["$suspends"] else []
      | _ => []
    here ++ e.children.flatMap (expr bound)

partial def top (bound : List String := []) : STop → List String
  | .fn _ _ ps tps es r b =>
    let bound := tps.map (·.name) ++ bound
    (if es.contains "suspends" then ["$suspends"] else []) ++ ty bound r ++ expr bound b ++
      ps.flatMap fun p => ty bound p.ty ++ p.default.toList.flatMap (expr bound)
  | .const _ _ t e => t.toList.flatMap (ty bound) ++ expr bound e
  | .classDef _ _ tps _ parents _ fs _ ms =>
    let bound := tps.map (·.name) ++ bound
    parents.flatMap (ty bound) ++
      fs.flatMap (fun (_, t, d, _) => ty bound t ++ d.toList.flatMap (expr bound)) ++
      ms.flatMap (top bound)

end OpenVerse.Front.PreludeNeeds
