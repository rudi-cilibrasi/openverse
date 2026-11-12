/-
  OpenVerse front end — overloaded methods' names (#106).

  A method name declared with two or more parameter lists in one class
  hierarchy (classes and interfaces connected by inheritance, so unrelated
  classes' methods of one name are not overloads) is renamed, in every class
  and interface of it, by its list: `M$ovK`, the K-th list of the hierarchy.
  An override has its method's list, so its name too. Lists are compared up
  to the names of type parameters (the class's and the method's own, each by
  its place, so a generic override that renames them has its method's list),
  and `string` is `[]char`.

  The elaborator renames them so (`MethodOverloads.apply`); methods with
  several values (`Choice.methodFns`, #283) name their families by the same
  lists, as a call of one takes the list the elaborator found it takes.
-/
import OpenVerse.Front.Syntax

namespace OpenVerse.Front

/-- The overloaded methods of a program's classes and interfaces. -/
structure MethodOverloads where
  /-- Each (hierarchy, method name) declared with several lists, and the
      lists, in order: `M$ovK` is the K-th. -/
  lists : List ((String × String) × List String)
  /-- Whether method `mn` is overloaded in the hierarchy of class `cn`. -/
  overloaded : (cn mn : String) → Bool
  /-- The name of method `mn` of class `cn` (whose type parameters are
      `ctps`) declared with type parameters `mtps` and parameters `ps`:
      `mn` when not overloaded, else `mn$ovK`, an override's (`isOverride`)
      that of the list above it that it has, and a qualified one's
      (`(q:)M`, `within`) one of `q`'s lists or those above it. `mn` when
      none fits, which `apply` refuses for a qualified one. -/
  name : (cn mn : String) → (ctps mtps : List TParam) → (ps : List SParam) → (isOverride : Bool) →
    (within : Option String) → String
  /-- Each class's ancestors, itself first. -/
  ancestors : String → List String

/-- The overloaded methods of the classes and interfaces of `tops`. -/
def MethodOverloads.of (tops : List STop) : MethodOverloads := Id.run do
  let sigText (ctps : List TParam) (mtps : List TParam) (ps : List SParam) : String :=
    let ρ : List (String × STy) :=
      ((ctps.zip (List.range ctps.length)).map fun (tp, i) => (tp.name, STy.name s!"$c{i}")) ++
      ((mtps.zip (List.range mtps.length)).map fun (tp, i) => (tp.name, STy.name s!"$m{i}"))
    -- (and `string` is `[]char`)
    let ρ := ρ ++ [("string", STy.arr (.name "char"))]
    reprStr (ps.map fun q => (q.named, if q.named then q.name else "", q.ty.substNames ρ))
  let classDefs : List (String × List TParam × List STy × List STop) := tops.filterMap fun
    | .classDef _ n tps _ parents _ _ _ methods => some (n, tps, parents, methods)
    | _ => none
  let parentName : STy → Option String := fun | .name q => some q | .app q _ => some q | _ => none
  let mut hier : List (String × String) := classDefs.map fun (n, _) => (n, n)
  for _ in [0:classDefs.length + 1] do
    -- (until a pass joins nothing: a pass per class made it cubic)
    let mut joined := false
    for (n, _, ps, _) in classDefs do
      for q in ps.filterMap parentName do
        match hier.lookup n, hier.lookup q with
        | some a, some b =>
          if a != b then
            let r := if a < b then a else b
            hier := hier.map fun (x, h) => if h == a || h == b then (x, r) else (x, h)
            joined := true
        | _, _ => pure ()
    if !joined then break
  let hierOf (n : String) : String := (hier.lookup n).getD n
  -- each class's ancestors (itself first), each with its type parameters in
  -- the class's terms
  let infoOf (n : String) := (classDefs.find? (·.1 == n)).map fun (_, tps, ps, ms) => (tps, ps, ms)
  let mut anc : List (String × List (String × List (String × STy))) :=
    classDefs.map fun (n, _) => (n, [(n, [])])
  for _ in [0:classDefs.length + 1] do
    let mut changed := false
    for (n, _, ps, _) in classDefs do
      let mine := (anc.lookup n).getD []
      let mut add : List (String × List (String × STy)) := []
      for pty in ps do
        let (q, args) := match pty with | .app q as => (q, as) | .name q => (q, []) | _ => ("", [])
        let qtps := ((infoOf q).map (·.1)).getD []
        let σq : List (String × STy) := (qtps.map (·.name)).zip args
        for (y, σy) in (anc.lookup q).getD [] do
          if !(mine ++ add).any (·.1 == y) then
            let σ := if y == q then σq else σy.map fun (v, t) => (v, t.substNames σq)
            add := add ++ [(y, σ)]
      if !add.isEmpty then
        anc := anc.map fun (x, a) => if x == n then (x, a ++ add) else (x, a)
        changed := true
    if !changed then break
  -- the non-override declarations of a method in a class: its lists
  let ownLists (y mn : String) : List (List TParam × List SParam) := ((infoOf y).map fun (_, _, ms) =>
    ms.filterMap fun
      | .fn _ x ps mtps effs .. => if x == mn && !effs.contains "override" then some (mtps, ps) else none
      | _ => none).getD []
  let decls : List ((String × String) × String) := classDefs.flatMap fun (cn, ctps, _, methods) =>
    methods.filterMap fun
      -- (an override joins its method's list: only the others make lists)
      | .fn _ mn ps mtps effs .. =>
        if mn == "$block" || mn.startsWith "(" || effs.contains "override" then none
        else some ((hierOf cn, mn), sigText ctps mtps ps)
      | _ => none
  let keys := (decls.map (·.1)).eraseDups
  -- (a name is overloaded where some class's ancestors declare two or more
  -- of its lists: siblings' own lists are not overloads)
  let listsSeen (n mn : String) : List String :=
    (((anc.lookup n).getD []).flatMap fun (y, _) =>
      let ytps := ((infoOf y).map (·.1)).getD []
      (ownLists y mn).map fun (mtps, ps) => sigText ytps mtps ps).eraseDups
  let mov : List ((String × String) × List String) := keys.filterMap fun key =>
    let sigs := ((decls.filter (·.1 == key)).map (·.2)).eraseDups
    if sigs.length > 1 && classDefs.any (fun (n, _) => hierOf n == key.1 && (listsSeen n key.2).length > 1) then
      some (key, sigs)
    else none
  let name (cn mn : String) (ctps mtps : List TParam) (ps : List SParam) (isOverride : Bool)
      (within : Option String) : String :=
    match mov.lookup (hierOf cn, mn) with
    | none => mn
    | some sigs =>
      if !isOverride then s!"{mn}$ov{(sigs.idxOf? (sigText ctps mtps ps)).getD 0}"
      else
        -- an override: the ancestor list it has, each in this class's terms
        -- (through the type arguments the class gives its parents)
        let mine := sigText ctps mtps ps
        -- (a qualified `(q:)M`: only `q`'s lists, and those above it)
        let none' : List (String × List (String × STy)) := []
        let ups0 : List (String × List (String × STy)) := ((anc.lookup cn).getD none').drop 1
        let ups : List (String × List (String × STy)) := match within with
          | some q =>
            let above : List String := ((anc.lookup q).getD none').map Prod.fst
            ups0.filter fun u => u.1 == q || above.contains u.1
          | none => ups0
        let cands : List (Nat × String × Nat) := ups.flatMap fun (y, σ) =>
          let ytps := ((infoOf y).map (·.1)).getD []
          (ownLists y mn).filterMap fun (dmtps, dps) =>
            (sigs.idxOf? (sigText ytps dmtps dps)).map fun k =>
              -- (its own type parameters renamed apart first: the class's
              -- arguments must not capture them)
              let apart : List (String × STy) := (dmtps.zip (List.range dmtps.length)).map fun (tp, i) =>
                (tp.name, STy.name s!"$own{i}")
              let dmtps' := (dmtps.zip (List.range dmtps.length)).map fun (tp, i) => { tp with name := s!"$own{i}" }
              (k, sigText ctps dmtps' (dps.map fun q => { q with ty := (q.ty.substNames apart).substNames σ }), dps.length)
        match (cands.filter (·.2.1 == mine)).map (·.1) |>.eraseDups with
        | [k] => s!"{mn}$ov{k}"
        | _ =>
          match (cands.filter (·.2.2 == ps.length)).map (·.1) |>.eraseDups with
          | [k] => s!"{mn}$ov{k}"
          | _ => mn   -- refused where it is checked
  return { lists := mov, name, overloaded := fun cn mn => (mov.lookup (hierOf cn, mn)).isSome,
           ancestors := fun n => ((anc.lookup n).getD [(n, [])]).map (·.1) }

/-- `tops` with each overloaded method's declarations renamed by their lists
    (`MethodOverloads.name`), a qualified one's `(q:)M$ovK` (#125). -/
def MethodOverloads.apply (mo : MethodOverloads) (tops : List STop) : Except String (List STop) :=
  tops.mapM fun
    | .classDef cp n tps specs parents isI fields ovs methods => do
      let ms ← methods.mapM fun
        | .fn mp mn ps mtps effs ret body => do
          -- `(q:)M`, implementing `q`'s overload of `M` that has its list
          -- (#125): `(q:)M$ovK`
          let qual : Option (String × String) := if mn.startsWith "(" then
              match (mn.drop 1).toString.splitOn ":)" with
              | [q, m'] => some (q, m')
              | _ => none
            else none
          match qual with
          | some (q, m') =>
            -- (`q` above the class: otherwise the elaborator's check explains)
            let isAbove := ((mo.ancestors n).drop 1).contains q
            if isAbove && mo.overloaded n m' then
              let k := mo.name n m' tps mtps ps true (some q)
              if k == m' then
                throw s!"{mp.show}: ({q}:){m'} must have the parameters of one of {q}'s overloads of {m'}"
              return .fn mp s!"({q}:){k}" ps mtps effs ret body
            else return .fn mp mn ps mtps effs ret body
          | none => return .fn mp (mo.name n mn tps mtps ps (effs.contains "override") none) ps mtps effs ret body
        | m => pure m
      return .classDef cp n tps specs parents isI fields ovs ms
    | t => pure t

end OpenVerse.Front
