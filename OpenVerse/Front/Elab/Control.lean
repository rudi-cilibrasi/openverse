/- Elaboration control; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.For
import OpenVerse.Front.Elab.Calls

namespace OpenVerse.Front
open OpenVerse
partial def elabSetWith (elabE : Ctx → SExpr → Option Ty → EM R) (elabMember : Ctx → Pos → R → String → EM R)
    (ctx : Ctx) (p : Pos) (lhs0 : SExpr) (op : Option String) (rhs0 : SExpr)
    (rootInit : Option (String × Expr) := none) : EM R := do
  if let .app _ (.ident _ "$refineCopyOut") [rhs] false := rhs0 then
    let r ← elabSetWith elabE elabMember ctx p lhs0 op rhs rootInit
    match r.e with
    | .assign target (.local result) =>
      modify fun st => { st with frameCopies := st.frameCopies ++ [{ target, result }] }
    | .assign target (.prim (.tupGet field) [.local result]) =>
      modify fun st => { st with frameCopies := st.frameCopies ++ [{ target, result, field := some field }] }
    | _ => eerr p "internal error: a refining copy-out is not a saved result"
    return r
  -- (`$withOld(O, R)`: for `op=`, the old value was read into `O` before
  -- the code that computes `R`, as `set` evaluates, #208)
  -- Private indexed adapters have already read/validated the leaf in the
  -- caller. Reading it again here would move bounds failure before the
  -- saved-value arithmetic, and prevent a map key deleted by the RHS
  -- from being reinserted. Legacy $withOld retains its source validation.
  let (rhs, oldIn, preloaded) ← match rhs0 with
    | .app _ (.ident _ "$choiceWithOld") [.ident _ o, r] false => do
      let some binding := ctx.lookup o | eerr p "internal: missing saved indexed value"
      pure (r, some (Expr.local binding.slot), true)
    | .app _ (.ident _ "$withOld") [.ident _ o, r] false =>
      pure (r, (ctx.lookup o).map (fun l => Expr.local l.slot), false)
    | r => pure (r, none, false)
  -- the right side at the target's type; for `set F *= N` of a float, an
  -- int too (#127), so without it when that fails
  let rhsAt (t : Ty) : EM R :=
    if op == some "*" && t == .float then
      tryCatch (elabE ctx rhs (some t)) fun _ => elabE ctx rhs none
    else elabE ctx rhs (some t)
  -- in a method, a path from a field of `Self` (as when one is read)
  let rec selfRoot : SExpr → SExpr
    | .ident ip n =>
      match ctx.lookup n, ctx.selfClass with
      | none, some c => if (ctx.types.fields c).any (·.1 == n) then .member ip (.ident ip "Self") n else .ident ip n
      | _, _ => .ident ip n
    | .member sp e f => .member sp (selfRoot e) f
    | .app sp e [k] true => .app sp (selfRoot e) [k] true
    | .query sp e => .query sp (selfRoot e)
    | e => e
  let lhs := selfRoot lhs0
  let combine (old0 : Expr) (ty : Ty) (o : String) (new0 : R) : EM Expr := do
    let old := oldIn.getD old0
    -- (a refinement's value is its base; a refined variable is set only
    -- through a cast, #136)
    let new := widenR (← get).env new0
    if let .refine n := ty then
      eerr p s!"set {o}= on {withArticle n} needs a cast: write set X = {n}[X {o} …], which fails when the result is not one"
    match o, ty, new.ty with
    | "+", .rational, _ => rationalBinary p .add ⟨old, ty⟩ new
    | "-", .rational, _ => rationalBinary p .sub ⟨old, ty⟩ new
    | "*", .rational, _ => rationalBinary p .mul ⟨old, ty⟩ new
    | "/", .rational, _ => rationalBinary p .quotient ⟨old, ty⟩ new
    | "+", .int, .int => pure (p2 .add old new.e)
    | "-", .int, .int => pure (p2 .sub old new.e)
    | "*", .int, .int => pure (p2 .mul old new.e)
    | "+", .arr t, .arr u => do
        if t == u then pure (p2 .concat old new.e)
        else if refUp (← get).env (.arr u) (.arr t) then pure (p2 .concat old (← coerce p new (.arr t)))
        else if u.hasNever then
          match ← tryCatch (some <$> coerce p new (.arr t)) (fun _ => pure none) with
          | some e => pure (p2 .concat old e)
          | none => eerr p s!"cannot concatenate {ty.show} and {new.ty.show}"
        else eerr p s!"cannot concatenate {ty.show} and {new.ty.show}"
    -- floats (#127)
    | "+", .float, .float => pure (p2 .fadd old new.e)
    | "-", .float, .float => pure (p2 .fsub old new.e)
    | "*", .float, .float => pure (p2 .fmul old new.e)
    | "*", .float, .int => pure (p2 .fmul old (.prim .fofInt [new.e]))
    | "/", .float, .float => pure (p2 .fdiv old new.e)
    | "/", .int, _ => eerr p "set /= is not defined on int (integer division can fail)"
    | _, _, _ => eerr p s!"no operator '{o}=' for {ty.show} and {new.ty.show}"
  let mutableLocal (n : String) : EM Local := do
    match ctx.lookup n with
    | some l => if l.mutable then pure l else eerr p s!"'{n}' is not a var; declare it with var {n}:t = …"
    | none => eerr p s!"unknown variable '{n}'"
  -- a path `X.F[i]…`: the root variable and its steps (`some f` a field,
  -- `none` with an expression an index or key)
  let rec path : SExpr → Option (String × List (Pos × Option String × Option SExpr))
    | .ident _ n => some (n, [])
    | .member sp e f => (path e).map fun (n, ss) => (n, ss ++ [(sp, some f, none)])
    | .app sp e [k] true => (path e).map fun (n, ss) => (n, ss ++ [(sp, none, some k)])
    -- `X?`: the value inside an option; fails when empty
    | .query sp e => (path e).map fun (n, ss) => (n, ss ++ [(sp, some "?", none)])
    | _ => none
  let general : List (Pos × Option String × Option SExpr) → Bool
    | steps@(_ :: _ :: _) => !steps.isEmpty
    | steps => steps.any (·.2.1 == some "?")
  let opaqueIndex (root : String) (steps : List (Pos × Option String × Option SExpr)) : Bool :=
    (ctx.lookup root).any (fun binding => match binding.ty with
      | .param .. => steps.any (fun (_, field, key) => field == some "?" || key.isSome)
      | _ => false)
  if let some (root, steps) := path lhs then if general steps || opaqueIndex root steps then
    -- `set X.p = e` with a path of two or more steps (Book of Verse §3.5, §9.3):
    -- the indices and keys are evaluated once, left to right; then each
    -- intermediate container is read (an index or an intermediate key that
    -- is missing makes the set fail); then the new leaf; then the
    -- containers are rebuilt from the leaf up, ending with the variable
    -- the variable must be a var unless the path writes an object (below)
    let l ← match ctx.lookup root with
      | some l => pure l
      | none => eerr p s!"unknown variable '{root}'"
    let mut pre : Array Expr := #[]
    -- per step: the container's slot and type, and the step
    let mut levels : Array (Nat × Ty × Pos × Option String × Option (Nat × Ty)) := #[]
    let mut cur := l.slot
    let mut ty := l.ty
    -- first the indices and keys
    let mut keys : Array (Option (Nat × Ty)) := #[]
    let mut tys : Array Ty := #[]
    let mut rawTys : Array Ty := #[]
    let mut views : Array (Option (Nat × R)) := #[]
    for (sp, f?, k?) in steps do
      rawTys := rawTys.push ty
      let mut view := none
      if let .param .. := ty then
        let input ← fresh ty
        let source : R := ⟨.local input, ty⟩
        let receiver ← match f?, k? with
          | some "?", _ => elabContainerReceiverWith elabE ctx sp source (fun | .opt _ => true | _ => false) "query"
          | some field, _ => elabBoundReceiverWith elabE ctx sp source field
          | none, some _ => elabContainerReceiverWith elabE ctx sp source (fun | .arr _ | .map .. => true | _ => false) "index"
          | _, _ => pure source
        if receiver.ty != ty then
          view := some (input, receiver)
          ty := receiver.ty
      views := views.push view
      tys := tys.push ty
      match f?, k?, ty with
      | some "?", _, .opt t => keys := keys.push none; ty := t
      | some "?", _, t => eerr sp s!"'?' in a set needs an option, found {t.show}"
      | some f, _, .struct sn targs =>
        match fieldIndex (ctx.types.fields sn targs) f with
        | some (_, ft) => keys := keys.push none; ty := ft
        | none => eerr sp s!"{ty.show} has no field '{f}'"
      | some f, _, t => eerr sp s!"{t.show} has no field '{f}'"
      | none, some k, .arr t =>
        let ri ← elabE ctx k (some .int)
        if ri.ty != .int then eerr sp "an array index must be an int"
        let ti ← fresh .int
        pre := pre.push (.assign ti ri.e)
        keys := keys.push (some (ti, .int)); ty := t
      | none, some k, .map kt vt =>
        let rk ← elabE ctx k (some kt)
        let tk ← fresh kt
        pre := pre.push (.assign tk (← coerce sp rk kt))
        keys := keys.push (some (tk, kt)); ty := vt
      | _, _, t => eerr sp s!"cannot index a value of type {t.show}"
    let leafTy := ty
    -- the last step from an object (#34): it writes the object in place, so
    -- the path above it is only read, and its field must be a var
    let tysA := tys
    let refLevel? : Option Nat := (List.range steps.length).reverse.find? fun k =>
      match tysA[k]! with
      | .struct sn _ => ctx.types.isRefClass sn
      | _ => false
    for (view, index) in views.toList.zipIdx do
      if let some (_, receiver) := view then
        let container := match receiver.ty with | .arr _ | .map .. | .opt _ => true | _ => false
        if container && !(refLevel?.any (index < ·)) then
          eerr p s!"cannot write through a container upper bound: source storage must retain {rawTys[index]!.show}"
    if let some kr := refLevel? then
      let (sp, f?, _) := steps.toArray[kr]!
      match tysA[kr]!, f? with
      | .struct sn _, some f =>
        if !ctx.types.isVarField sn f then eerr sp (classSetMsg sn f)
      | _, _ => eerr p "internal: set path"
    if refLevel?.isNone && !l.mutable then
      eerr p s!"'{root}' is not a var; declare it with var {root}:t = …"
    -- read one step of the container in slot `c` of type `cty`
    let readStep (c : Nat) (cty : Ty) (step : Option String) (key : Option (Nat × Ty)) : EM Expr := do
      match step, key, cty with
      | some "?", _, .opt _ => pure (.prim .query [.local c])
      | some f, _, .struct sn targs =>
        -- a class's field as when it is read (an interface field may sit at
        -- different places in different classes)
        if ctx.types.classes.contains sn then return (← elabMember ctx p ⟨.local c, cty⟩ f).e
        let (j, _) := (fieldIndex (ctx.types.fields sn targs) f).get!
        pure (.prim (.tupGet j) [.local c])
      | none, some (ti, _), .arr _ => pure (p2 .index (.local c) (.local ti))
      | none, some (tk, kt), .map _ vt =>
        let tp ← fresh (.tup [kt, vt])
        pure (mapLookup c tk tp)
      | _, _, _ => eerr p "internal: set path"
    -- A view consumes the already-read source container. Its dictionary
    -- call belongs here in traversal, not in the index/key prelude.
    let activate (k current : Nat) : EM (List Expr × Nat) := do
      match views[k]! with
      | none => return ([], current)
      | some (input, receiver) =>
        let output ← fresh receiver.ty
        return ([.assign input (.local current), .assign output receiver.e], output)
    if let some (name, value) := rootInit then
      if name != root then eerr p "internal: bound set initializes a different path root"
      pre := pre.push (.assign l.slot value)
    -- a value of a class with no instance cannot exist, so the set is
    -- unreachable once the path reaches one; but the steps before it (the
    -- indices and keys, then the containers read) may fail first (#104)
    if let some ke := (List.range steps.length).find? fun k =>
        match tysA[k]! with | .struct sn _ => ctx.types.isEmptyClass sn | _ => false then
      let stepsA := steps.toArray
      let mut c := l.slot
      for k in [0:ke + 1] do
        let (before, viewed) ← activate k c
        pre := pre ++ before.toArray
        c := viewed
        if k < ke then
          let (_, f?, _) := stepsA[k]!
          let c' ← fresh rawTys[k + 1]!
          pre := pre.push (.assign c' (← readStep c tysA[k]! f? keys[k]!))
          c := c'
      -- (the right-hand side never runs, but is checked, and the field set
      -- at the empty class must be a var, as on any path)
      let lastCls := (List.range steps.length).reverse.find? fun k =>
        match tysA[k]!, stepsA[k]! with
        | .struct sn _, (_, some f, _) => f != "?" && ctx.types.classes.contains sn
        | _, _ => false
      if let some kc := lastCls then
        if let (.struct sn _, (sp, some f, _)) := (tysA[kc]!, stepsA[kc]!) then
          if !ctx.types.isVarField sn f then eerr sp (classSetMsg sn f)
      let r ← rhsAt leafTy
      match op with
      | none => discard <| coerce p r leafTy
      | some o => discard <| combine (.prim .userErr []) leafTy o r
      let tu ← fresh leafTy
      return ⟨pre.toList.foldr Expr.seq (.assign tu (.prim .userErr [])), leafTy⟩
    -- the intermediate containers: level 0 is a copy of the variable, taken
    -- after the indices, so that the right-hand side cannot change what is
    -- rebuilt (as for `set A[i] = e`); the variable is written once, last
    let c0 ← fresh l.ty
    pre := pre.push (.assign c0 (.local l.slot))
    cur := c0
    let stepsA := steps.toArray
    -- with an object on the path, the right-hand side runs once the path has
    -- reached it, before the values in the object are read (#34): a write it
    -- makes through the object is not lost. Without, it runs after every
    -- container is read, as for `set A[i] = e`.
    let rhsAfter : Nat := match refLevel? with
      | some kr => kr
      | none => stepsA.size
    let mut rhsVal : Option R := none
    let mut oldLeaf : Option Nat := none
    for k in [0:stepsA.size] do
      let (sp, f?, _) := stepsA[k]!
      let (before, viewed) ← activate k cur
      pre := pre ++ before.toArray
      cur := viewed
      levels := levels.push (cur, tys[k]!, sp, f?, keys[k]!)
      if k == rhsAfter then
        -- `set P op= e` reads P before e, as the direct form does (Book of
        -- Verse: `set X += e` is `set X = X + e`; #58): the rest of the path,
        -- read now, gives the old leaf (it fails as `P` would, and is read
        -- again for the rebuild below)
        if op.isSome && !preloaded then
          let mut c2 := cur
          for k2 in [k:stepsA.size] do
            if k2 > k then
              let (before, viewed) ← activate k2 c2
              pre := pre ++ before.toArray
              c2 := viewed
            let (_, f2, _) := stepsA[k2]!
            let t2 := if k2 + 1 < stepsA.size then rawTys[k2 + 1]! else leafTy
            let c3 ← fresh t2
            pre := pre.push (.assign c3 (← readStep c2 tys[k2]! f2 keys[k2]!))
            c2 := c3
          oldLeaf := some c2
        let r ← rhsAt leafTy
        let tr ← fresh r.ty
        pre := pre.push (.assign tr r.e)
        rhsVal := some ⟨.local tr, r.ty⟩
      if k + 1 < stepsA.size then
        let c ← fresh rawTys[k + 1]!
        pre := pre.push (.assign c (← readStep cur tys[k]! f? keys[k]!))
        cur := c
    let (lc, lty, _, lf, lkey) := levels[levels.size - 1]!
    -- a last `?` step also needs the option to be set
    if lf == some "?" then pre := pre.push (.seq (.prim .query [.local lc]) (.lit .void))
    -- the new leaf value
    let r ← match rhsVal with
      | some r => pure r
      | none => rhsAt leafTy
    let leaf ← match op with
      | none => coerce p r leafTy
      | some o =>
        -- (only an `op=` reads the old value: a read can have an effect)
        let old ← if preloaded then pure (oldIn.getD (.prim .userErr [])) else
          match oldLeaf with
            | some t => pure (Expr.local t)
            | none => readStep lc lty lf lkey
        combine old leafTy o r
    let tv ← fresh leafTy
    pre := pre.push (.assign tv leaf)
    -- rebuild, from the leaf up, as far as the object written in place
    let mut newVal : Expr := .local tv
    let mut wroteObject := false
    for k' in [0:levels.size] do
      let k := levels.size - 1 - k'
      if wroteObject then break
      let (c, cty, _, f?, key) := levels[k]!
      match f?, key, cty with
      | some "?", _, .opt _ => pre := pre.push (.assign c (.prim .mkSome [newVal]))
      | some f, _, .struct sn targs =>
        if ctx.types.isRefClass sn then
          let (j, ft) := (fieldIndex (ctx.types.fields sn targs) f).get!
          pre := pre.push (← setFieldAt ctx.types p sn targs c f j ft newVal)
          noteFx p ["writes"]
          wroteObject := true
        else
          let fs := ctx.types.fields sn targs
          let (j, _) := (fieldIndex fs f).get!
          let parts := (List.range fs.length).map fun i =>
            if i == j then newVal else Expr.prim (.tupGet i) [.local c]
          pre := pre.push (.assign c (.prim .mkTup parts))
      | none, some (ti, _), .arr _ =>
        pre := pre.push (.assign c (.prim .arrSet [.local c, .local ti, newVal]))
      | none, some (tk, _), .map _ vt =>
        -- the last key inserts or updates; an intermediate one was read above, so it exists
        let tvk ← fresh vt
        let ti ← fresh .int
        let tidx ← fresh .int
        pre := pre.push (.assign tvk newVal)
        pre := pre.push (mapPut c tk tvk ti tidx)
      | _, _, _ => eerr p "internal: set path"
      newVal := .local c
    if !wroteObject then pre := pre.push (.assign l.slot (.local c0))
    return ⟨pre.toList.foldr Expr.seq (.local tv), leafTy⟩
  match lhs with
  | .ident _ n =>
    let l ← mutableLocal n
    let r ← rhsAt l.ty
    let v ← match op with
      | none => coerce p r l.ty
      | some o => combine (.local l.slot) l.ty o r
    return ⟨.assign l.slot v, l.ty⟩
  | .app _ (.ident _ n) [k] true =>
    let l ← mutableLocal n
    match l.ty with
    | .map kt vt =>
      let rk ← elabE ctx k (some kt)
      let tk ← fresh kt
      let tp ← fresh (.tup [kt, vt])
      let r ← rhsAt vt
      let v ← match op with
        | none => coerce p r vt
        -- `set M[k] op= v` fails when k is not a key (Book of Verse §9.3)
        | some o => combine (mapLookup l.slot tk tp) vt o r
      let tv ← fresh vt
      let ti ← fresh .int
      let tidx ← fresh .int
      return ⟨.seq (.assign tk (← coerce p rk kt)) (.seq (.assign tv v)
        (.seq (mapPut l.slot tk tv ti tidx) (.local tv))), vt⟩
    | .arr t =>
      let i := k
      let ri := widenR ctx.types (← elabE ctx i (some .int))
      if ri.ty != .int then eerr p "an array index must be an int"
      let ti ← fresh .int
      let tv ← fresh t
      let r ← rhsAt t
      let v ← match op with
        | none => coerce p r t
        | some o => combine (p2 .index (.local l.slot) (.local ti)) t o r
      -- `set A[i] = v` fails out of range and returns `v` (Book of Verse §3.3)
      return ⟨.seq (.assign ti ri.e)
        (.seq (.assign l.slot (.prim .arrSet [.local l.slot, .local ti, .assign tv v])) (.local tv)), t⟩
    | ty => eerr p s!"cannot index a value of type {ty.show}"
  | .member _ (.ident _ n) f =>
    -- an object's field: written in place, through any variable (#34)
    if let some l := ctx.lookup n then
      if let .struct sn _ := l.ty then
        if ctx.types.isRefClass sn then
          let targs := match l.ty with | .struct _ ts => ts | _ => []
          let some (k, t) := fieldIndex (ctx.types.fields sn targs) f
            | eerr p s!"class {sn} has no field '{f}'"
          if !ctx.types.isVarField sn f then eerr p (classSetMsg sn f)
          let r ← rhsAt t
          noteFx p (if op.isSome then ["reads", "writes"] else ["writes"])
          let v ← match op with
            | none => coerce p r t
            -- (the current value, read as a read does)
            | some o => combine (← elabMember ctx p ⟨.local l.slot, l.ty⟩ f).e t o r
          return ⟨← setFieldAt ctx.types p sn targs l.slot f k t v, t⟩
    if let some l := ctx.lookup n then
      if let .struct sn targs := l.ty then
        if ctx.types.isEmptyClass sn then
          -- no instance can exist: unreachable
          let some (_, t) := fieldIndex (ctx.types.fields sn targs) f | eerr p s!"class {sn} has no field '{f}'"
          let tu ← fresh t
          return ⟨.assign tu (.prim .userErr []), t⟩
        if ctx.types.classes.contains sn && !ctx.types.isRefClass sn then
          eerr p s!"field '{f}' of the parametric class {sn} cannot be set: a parametric class is a value (#34)"
    let l ← mutableLocal n
    match l.ty with
    | .struct sn targs =>
      if ctx.types.classes.contains sn then eerr p (classSetMsg sn f)
      let fs := ctx.types.fields sn targs
      match fieldIndex fs f with
      | some (k, t) =>
        let r ← rhsAt t
        let v ← match op with
          | none => coerce p r t
          | some o => combine (.prim (.tupGet k) [.local l.slot]) t o r
        let tv ← fresh t
        -- the struct is rebuilt with field k replaced; `set` returns the new field value
        let parts := (List.range fs.length).map fun i =>
          if i == k then Expr.assign tv v else Expr.prim (.tupGet i) [.local l.slot]
        return ⟨.seq (.assign l.slot (.prim .mkTup parts)) (.local tv), t⟩
      | none => eerr p s!"struct {sn} has no field '{f}'"
    | ty => eerr p s!"{ty.show} has no field '{f}'"
  | _ => eerr p "openverse supports set X = …, and set on a path of fields, indices and keys from a variable (set S.F[i].G = …); not through a tuple element or a call result"

/-- `if (D := T[X]) then Body else Else`, where the cast holds only under a
    refinement of the code's type parameters (#243). `Body` is lifted into
    a generic function (`Refine.functions`), asked for in a first
    elaboration, which elaborates `Body` in the refined world to find its
    type, effects and the locals it uses. Then the `if` is a dispatch to
    it, one test per set of pins among the classes tested, as a refined
    method call is: `Typed.dispatch` types the call under the refinement,
    with the object (as `D`) and those locals passed at their refined
    types. `none` when the cast does not refine: the plain path. With
    `ifType`, only the `if`'s type with no expected type, as any `if`'s
    (`ifBranches`), and in its code, as a `logic`, whether its branch is
    elaborated at that type, not its own. -/
partial def elabRefinedIfWith (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (elabE : Ctx → SExpr → Option Ty → EM R) (withMark : Ctx → Expr → EM Expr) (ctx : Ctx) (p _dp : Pos) (D T : String) (x : SExpr) (body0 : SExpr)
    (elseE : Option SExpr) (exp : Option Ty) (made : Bool := false)
    (escRet : Option (Ty × Refine.Exits) := none)
    (outsideWrites : List Nat := []) (ifType : Bool := false) :
    EM (Option R) := do
  let ctx := ctx.choiceCoercionScope
  -- (the lift's tag is of the branch as written, before choice conversions
  -- wrap it, as `elabExprControlWith` computes it too)
  let written := body0
  let body0 := ctx.choiceCoercionBody body0
  let env := ctx.types
  if !env.classes.contains T then return none
  -- (in a method: the members of `Self` the branch names bare, as members
  -- of `Self`, which its function takes as a parameter)
  let body := match ctx.selfClass with
    | some c => selfQualify ctx c body0
    | none => body0
  let st0 ← get
  let rx ← elabE { ctx with canFail := true, inTaking := true } x none
  let some (S, sargs, targs, common, eqs, opened) := refiningCast? env T rx.ty (env.tvars.map (·.1))
    | do set st0; return none
  -- (#53, #351: to a type beside the object's, or to an interface whose type
  -- arguments it opens: a cast to each class below both, whose branch calls
  -- this one's function, which takes `T`'s type arguments' values)
  let chain := castChains env S T opened
  if !env.isRefClass S || (!opened.isEmpty && !env.isRefClass T) then set st0; return none
  -- (#250: `T` has Verse Core type arguments past the object's, or not as
  -- its own type parameters: its tests open them, as a method's dispatch does)
  let wide := !((env.coreVars T).length == (env.coreArgs S sargs).length &&
    (env.coreVars T).all fun (v, _) => !v.startsWith "$arg")
  let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
    if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
  let some (μT, opened) := castRefinement? env eqs opened (env.comparableArgs T targs) | do set st0; return none
  let targs := targs.map fun t => t.subst (opened.filterMap fun (n, _, c) => if c then some (n, Ty.param n true) else none)
  let shown := (Ty.struct T targs).show
  -- (the world under the refinement: the object as a `T`, in `dslot`, the
  -- locals and the code's type parameters refined, and the type arguments
  -- the cast opens, #250)
  let refine (t : Ty) : Ty := t.subst μT
  let dTy := refine (.struct T targs)
  let refined (dslot : Nat) : Ctx := { ctx with
    locals := { name := D, slot := dslot, ty := dTy, mutable := false } ::
      ctx.locals.map fun l => { l with ty := refine l.ty, storage := l.storage.map (·.subst μT) },
    types := { env with tvars := (env.tvars.map (fun (n, t) => (n, refine t)) ++
      opened.map (fun (n, _, c) => (n, Ty.param n c))) } }
  -- (the branch's type under the refinement, as code outside it names it: a
  -- local it gives at its own type there, the most general)
  let own (v : SExpr) (t : Ty) : Ty := match v with
    | .ident _ n => if Refine.isCastObj n then ((ctx.lookup n).map (·.ty)).getD (refine t) else refine t
    | _ => refine t
  let branchTyOf (t : Ty) : Ty := match Refine.valueOf body, t with
    | .tuple _ vs, .tup ts => if vs.length == ts.length then .tup ((vs.zip ts).map fun (v, t) => own v t) else refine t
    | v, t => own v t
  -- (with no expected type, the `if`'s type is any `if`'s, `ifBranches`,
  -- its branch typed under the refinement: at a type asked for, when it is
  -- one there, else at its own; the same in every elaboration, which may
  -- find the branch's function made or not; nothing is kept. The branch's
  -- own type is one under the refinement, which code outside it may name
  -- otherwise: one that is the `else`'s there makes the `if` the `else`'s,
  -- as their join, before any other comparison. And whether the branch
  -- must be elaborated at that type: when it has none alone, or its own
  -- does not join into it there, `if (C) then false else option{4}`, `if
  -- (C) then 1 else "a"`, at `any`)
  let ifTyAt (ee : SExpr) : EM (Ty × Bool) := do
    let st ← get
    let thenAt (k : Nat) (e : Option Ty) : EM R := do
      let rb ← elabE { refined (← fresh dTy) with typeOnly := true, retries := k } (Refine.exitsAsErr body) (e.map refine)
      let fits ← match e with
        | some t => tryCatch (do discard <| coerce p rb (refine t); pure true) fun _ => pure false
        | none => pure false
      return ⟨rb.e, if fits then e.getD rb.ty else branchTyOf rb.ty⟩
    let elseAt (k : Nat) (e : Option Ty) : EM R := elabE { ctx with typeOnly := true, retries := k } ee e
    let own? ← tryCatch (some <$> thenAt ctx.retries none) fun _ => pure none
    let re? ← tryCatch (some <$> elseAt ctx.retries none) fun _ => pure none
    let fitsElse ← match re? with
      | some re => tryCatch (do pure ((← thenAt ctx.retries (some re.ty)).ty == re.ty)) fun _ => pure false
      | none => pure false
    let τ ← match re?, fitsElse with
      | some re, true => pure re.ty
      | _, _ => ifBranches p none ctx.retries thenAt elseAt fun _ _ ty => pure ty
    let env' := (← get).env
    set st
    return (τ, own?.all fun b => joinTy env' b.ty (refine τ) none != some (refine τ))
  let ifTy (ee : SExpr) : EM Ty := return (← ifTyAt ee).1
  if ifType then
    let (τ, atType) ← ifTyAt (elseE.getD (Refine.noValue p))
    return some ⟨.lit (.logic atType), τ⟩
  -- (the locals the branch uses, in order of first use)
  let caps : List Local := ctx.captureEvidence ((Choice.namesUsed body).filterMap fun n =>
    if n == D then none else ctx.locals.find? (·.name == n)) [D]
  -- (the `var`s from outside it that the branch sets, its `return`s and its
  -- `break`s that leave it, `refineExits`: copies in the branch, and its
  -- function returns what they say, which the caller does after the `if`;
  -- not again for the branch made so, whose `return`s are its function's,
  -- `escRet`)
  let setOut := caps.filter fun l => l.mutable && (Refine.findPart (fun
      | .set _ lhs _ _ => Choice.rootName? lhs == some l.name
      | _ => false) false body).isSome
  if let some (q, what) := refineBranchWhy? ctx p body ((caps.filter (·.mutable)).map (·.name) |>.filter fun n => !setOut.any (·.name == n))
      (allowEsc := true) then
    eerr q s!"the branch of the cast to {shown}, which holds only under a refinement of the type arguments, is compiled as a function of its own, so {what} (#243)"
  let retPart := Refine.findPart (fun | .ret .. => true | _ => false) false body
  let brkPart := Refine.findPart Refine.isBreak true body
  let escapes := retPart.isSome || brkPart.isSome
  if escRet.isNone && (!setOut.isEmpty || escapes) then
    -- (the `if`'s value: by its type where it is; with none there, the
    -- `else`'s, found apart, `void` carrying nothing)
    let vm? : Option ExitVal ← match elseE, exp with
      | none, _ => pure (some .none)
      | some _, some .void => pure (some .none)
      | some _, some t => pure (some (if escapes then .opt t.toSTy else .raw (some t.toSTy)))
      | some ee, none =>
        if escapes && escapesAlways (Choice.stmtsOf body) then pure (some .elseAfter)
        else do
          let st ← get
          let τe? ← tryCatch (do pure (some (← elabE { ctx with typeOnly := true } ee none).ty)) fun _ => pure none
          set st
          -- (the `if`'s type, as any `if`'s; for an `else` that gives no
          -- value, the branch's own, if code outside it can name it)
          let r? ← tryCatch (some <$> ifTyAt ee) fun _ => pure none
          let τ? := r?.map (·.1)
          let names (τ : Ty) : Bool := !opened.any fun (n, _, _) => τ.params.contains n
          let own? := if τe? == some .never then τ?.filter names else none
          let τ? := if τe? == some .never then own? else τ?
          if !escapes then
            -- Discard a statement's value before building the copy-out tuple.
            -- (the value at the `if`'s type, unless the new `if`, of tuples,
            -- finds it: the `else`'s, which the branch's own joins)
            let at? := own?.orElse fun _ => if τ? == τe? && r?.any (!·.2) then none else τ?
            pure (some (if τ?.any (· == .void) then .none else .raw (at?.map Ty.toSTy)))
          else
            pure (τ?.bind fun τ => if τ == .never then none
              else some (if τ == .void then ExitVal.none else .opt τ.toSTy))
    let some vm := vm?
      | eerr ((retPart.orElse fun _ => brkPart).map (·.pos) |>.getD p) s!"the branch of the cast to {shown}, which holds only under a refinement of the type arguments, is compiled as a function of its own, so it cannot return or break out of it yet where the if's value is used at a type not known there (write it) (#243)"
    let sourceRet ← match ctx.refineExits.ret with
      | some (some (_, t), _) => resolveTy env p t
      | some (none, _) => pure .void
      | none => match ctx.forReturnSlot.bind ctx.lookup with
        | some { ty := .opt t, .. } => pure t
        | _ => pure ctx.retTy
    let retS := if sourceRet == .void then none else some sourceRet.toSTy
    let (thenB, elseB, tupS, t, after, exits) := refineExits p body0 elseE (setOut.map fun l => (l.name, l.ty.toSTy))
      retPart.isSome brkPart retS vm
    set st0
    let tupTy ← tupS.mapM (resolveTy env p ·)
    -- (the new branch is the elaborator's, so its function is made from it,
    -- `made`, not from the source)
    let some rIf ← elabRefinedIfWith elabApp elabE withMark ctx p _dp D T x thenB (some elseB) tupTy (made := true)
        (escRet := if escapes then tupTy.map (·, exits) else none) (outsideWrites := outsideWrites ++ setOut.map (·.slot))
      | eerr p s!"internal: the cast to {shown} with sets, returns or breaks in its branch (#243)"
    let slot ← fresh rIf.ty
    let c := { ctx with locals := { name := t, slot, ty := rIf.ty, mutable := false } :: ctx.locals }
    let rest ← elabE c (.block p after) exp
    return some ⟨.seq (.assign slot rIf.e) rest.e, rest.ty⟩
  -- (a suspension in the branch makes its function `<suspends>`, whose
  -- dispatch the lowering takes as a suspends method's call, #243; the
  -- `else` is the caller's code, which may suspend as any)
  let isS (f : Nat) : Bool := ctx.sigs.any fun s => s.idx == f && s.suspends
  let immediateLifts := env.castRequests.filter (!·.waits) |>.map (·.name)
  -- Cancellation itself is immediate. Keep scanning its receiver.
  let mayWait (f : Nat) : Bool :=
    ctx.sigs.any fun s => s.idx == f && s.suspends && s.name != "$cancelMark" && !immediateLifts.contains s.name
  let startsTask (f : Nat) : Bool :=
    ctx.sigs.any fun s => s.idx == f && (s.name == "$spawnMark" || s.name == "$branchMark")
  let waits (e : Expr) : Bool := Suspend.countSusp mayWait (fun _ => false) false startsTask e > 0
  let elseOf : EM R := match elseE with
    | none => pure ⟨.lit .void, .void⟩
    | some ee => elabE ctx ee exp
  let tag := refineTagOf ctx x written elseE exp
  let key := Refine.keyOf p D tag
  let liftName := s!"$refine{p.line}_{p.col}_{D}" ++ (if p.file.isEmpty then "" else s!"_{p.file}") ++ tag
  -- Keep a suspending lift's available parameters in a stable order from
  -- discovery onward: locals it declares may themselves be borrowed by a
  -- nested lift, whose frame reference needs exactly this argument order.
  let availableTypes : List Ty := env.tvars.map (fun binding => Ty.subst μT binding.2) ++
    opened.map (fun binding => Ty.param binding.1 binding.2.2)
  let available := Ty.mergeParamBounds (availableTypes.flatMap Ty.paramsC)
  match env.castRequests.find? (·.key == key) with
  | none =>
    -- (first: the branch in the refined world)
    let dslot ← fresh dTy
    let ctxB : Ctx := { (refined dslot).withTrial .branch with
      frameName := liftName, frameArgs := available.map fun (n, c) => Ty.param n c,
      -- (the source return's value and the lifted function's copy-out)
      retTy := (escRet.map (refine ·.1)).getD ctx.retTy,
      refineExits := (escRet.map (·.2)).getD {},
      defers := if escRet.isSome then [] else ctx.defers }
    -- (its own effects, which its function declares; the enclosing one's too)
    let fx0 := (← get).fx
    let pending0 := (← get).pendingSuspendingCasts
    let waiting0 := (← get).pendingWaitingCasts
    let source0 := (← get).pendingSourceSuspends
    let background := (← get).backgroundSlots
    modify fun st => { st with fx := [] }
    let retarget (h : ConstructHint) : ConstructHint :=
      if h.frame == ctx.frameName then { h with frame := liftName } else h
    let ctxB := { ctxB with constructHints := ctxB.constructHints.map (·.map retarget) }
    let body := pruneConstructHints ctxB liftName
      (pruneConstructHints { ctxB with frameName := ctx.frameName } liftName body)
    -- (with no expected type, at the `if`'s, `ifTy`, as an `if`'s branches
    -- are: `false` against an `else`'s option is its empty one)
    let τ? : Option Ty ← match elseE, exp with
      | some ee, none => some <$> ifTy ee
      | _, _ => pure none
    let rb ← elabE ctxB body (if elseE.isNone then some .void else (exp.orElse fun _ => τ?).map refine)
    let waitingThen := (← get).pendingWaitingCasts
    let thenWaits := ctx.suspends && (waitingThen != waiting0 || waits rb.e)
    let sourceSuspends := ctx.suspends && ((← get).pendingSourceSuspends != source0 || ctx.sourceWaits rb.e)
    if thenWaits then
      for l in caps do
        if l.mutable && l.storage.isNone && (background.contains l.slot || outsideWrites.contains l.slot) then
          eerr p s!"internal error: a suspending mutable capture '{Choice.shownName l.name}' has no source storage"
    let fxB := (← get).fx
    modify fun st => { st with fx := fx0 }
    for (k, q, via) in fxB do noteFx q [k] via
    let re ← elseOf
    -- Preserve the dispatch shape when lowering either side. Task starts
    -- need lowering too, but only a wait exposes copies of shared slots.
    let hasPending := (← get).pendingSuspendingCasts != pending0
    let needsFrame (f : Nat) := isS f || ctx.sigs.any (fun s => s.idx == f && s.name == "$branchMark")
    let suspendsB := ctx.suspends && (hasPending || Suspend.hasSusp needsFrame rb.e || Suspend.hasSusp needsFrame re.e)
    let elseWaits := ctx.suspends && ((← get).pendingWaitingCasts != waitingThen || waits re.e)
    -- (an `else` that gives no value, as the rest of a failure context has,
    -- `elabSeqIn`: the branch's type, which code outside it must be able to
    -- name)
    let retOfBranch := elseE.isSome && exp.isNone && re.ty == .never
    let branchTy := branchTyOf rb.ty
    let τ' : Ty ← match elseE, exp with
      | none, _ => pure .void
      | some _, some t => pure t
      | some ee, none => if retOfBranch then pure branchTy else match τ? with
        | some t => pure t
        | none => ifTy ee
    if let some (n, v, _) := opened.find? fun (n, _, _) => τ'.params.contains n then
      eerr p s!"cannot cast {withArticle rx.ty.show} to {T} here: the cast opens {T}'s type argument {v} for the code after it, outside which its value, {withArticle τ'.show}, would name what is unknown (#250)"
    let ret := refine τ'
    -- (a branch whose value names an opened type argument where the `if`'s
    -- type, which code outside it has, cannot: refused as such, #250)
    discard <| tryCatch (coerce p rb ret) fun err => do
      if let some (_, v, _) := opened.find? fun (n, _, _) => rb.ty.params.contains n then
        eerr p s!"cannot cast {withArticle rx.ty.show} to {T} here: the cast opens {T}'s type argument {v} for its branch, whose value, {withArticle rb.ty.show}, would name what is unknown outside it, where the if's value is {withArticle τ'.show} (#250)"
      throw err
    let decides := rb.e.mayFail ctx.sigProg
    let sig := caps.map fun l => (l.name, refine l.ty)
    let tps := Ty.mergeParamBounds ((dTy :: ret :: sig.map (·.2)).flatMap Ty.paramsC)
    -- (the type parameters only the types written in the branch mention:
    -- each through a parameter of its own, passed a value of it, so that
    -- the call determines it)
    let written := ((Refine.typeNames body).filterMap fun w =>
      (env.tvars.lookup w).map refine).flatMap Ty.paramsC
    let storage := caps.filterMap fun l => l.storage.map fun s =>
      (l.name, s.subst μT)
    let storageTypes := (storage.flatMap (fun (_, s) => s.args)).flatMap Ty.paramsC
    let wanted := (if ctx.suspends then available else []) ++ storageTypes ++ written
    let allTps := Ty.mergeParamBounds (tps ++ wanted)
    let extra := allTps.filter fun (n, _) => !tps.any (·.1 == n)
    let tps := Ty.mergeParamBounds (if ctx.suspends then available ++ allTps else allTps)
    -- (the opened ones' values come from the object's hidden fields; those
    -- of a cast this one is in, from its function's, #250)
    if let some (n, _) := tps.find? fun (n, _) =>
        !ctx.dictVars.contains n && !opened.any (·.1 == n) && !ctx.types.tvars.any (·.1 == n) then
      eerr p s!"cannot lift the branch of the cast to {shown} yet: its types mention {n}, which this function has no value of (#243)"
    -- (from the enclosing function's own names, also through the
    -- refinements of the casts this one is in, as the branch is taken from
    -- the source)
    let σ := env.tvars.filterMap fun (n, t) =>
      let t' := refine t
      match t' with
      | .param m _ => if m == n then none else some (n, t'.toSTy)
      | _ => some (n, t'.toSTy)
    let heap := ["reads", "writes", "allocates"].filter fun k => fxB.any (·.1 == k)
    let specs := (if heap.isEmpty then ["computes"] else heap) ++ (if decides then ["decides"] else []) ++
      (if suspendsB then ["suspends"] else [])
    let lift : Refine.Lift := {
      pos := p, bound := D, target := if chain then "" else T, tag, continuationScope := ctx.refineScope,
      name := liftName,
      params := { name := D, ty := dTy.toSTy } ::
        (caps.zip sig).map (fun (binding, (name, ty)) => { name, ty := ty.toSTy, typeValue := binding.typeValue }) ++
        extra.map fun (n, _) => { name := s!"$type{n}", ty := .name n, typeValue := true },
      tparams := tps.map fun (n, c) => { pos := p, name := n, constraint := if c then "comparable" else "type" },
      specs, ret := ret.toSTy, branchTy := if retOfBranch then some τ'.toSTy else none, subst := σ, opened := if chain then [] else opened.map fun (n, v, _) => (n, v), waits := thenWaits, sourceSuspends,
      exits := Refine.Exits.substTypes ((escRet.map (·.2)).getD {}) σ,
      storage := storage.map fun (n, s) => (n, { frame := s.frame, name := s.name, args := s.args.map Ty.toSTy }),
      inRepeat := ctx.inRepeat, sourceContext := sourceContextOf ctx, liftTag := some ctx.liftTag,
      inlineScopes := ctx.inlineScopes,
      -- (made: a branch the elaborator made, for a cast with clauses
      -- after it, #286, which the source does not have as such)
      -- (and a tagged one, which the source's places do not find, #53)
      body := if ctx.selfClass.isSome || made || D.startsWith "$" || !tag.isEmpty || !ctx.choiceCoercions.isEmpty then some (pruneConstructHints ctxB liftName
        (pruneConstructHints { ctxB with frameName := ctx.frameName } liftName body)) else none }
    if ctx.keepsLifts then noteNeeds { casts := [lift] }
    if suspendsB then
      modify fun st => { st with pendingSuspendingCasts := st.pendingSuspendingCasts + 1 }
    if thenWaits || elseWaits then
      modify fun st => { st with pendingWaitingCasts := st.pendingWaitingCasts + 1 }
    if sourceSuspends || ctx.sourceWaits re.e then
      modify fun st => { st with pendingSourceSuspends := st.pendingSourceSuspends + 1 }
    -- (a placeholder: this elaboration goes no further; it may fail where
    -- the dispatch may, in the branch's function or in the `else`)
    return some ⟨if decides || re.e.mayFail ctx.sigProg then .prim .fail [] else .prim .userErr [], τ'⟩
  | some l =>
    let argOf (sp : SParam) : SExpr :=
      if sp.name.startsWith "$type" then .app p (.ident p "$witness") [.ident p (sp.name.drop 5).toString] false
      else .ident p sp.name
    if chain then
      -- (#53, #351: then a cast of the object to each class below both, the
      -- topmost of its class chain there, as a cast of its own (plain,
      -- refining or opening), whose branch calls the function with the
      -- object, which it gives `T`'s type arguments as that class has them,
      -- with their values; the object in a slot first, evaluated where a
      -- test of all those classes is, so that its effects roll back and its
      -- failure takes the else when none is the object's)
      let (pre, y) ← match rx.e with
        | .local y => pure ([], y)
        | e => do
          let y ← fresh rx.ty
          pure ([Expr.assign y e], y)
      -- (named by the place and the bound name, which tell apart the casts
      -- of one condition, as their lifts' keys do)
      let obj := s!"$castChain{p.line}_{p.col}_{D}"
      let ctxO := { ctx with locals := { name := obj, slot := y, ty := rx.ty, mutable := false } :: ctx.locals }
      let err : SExpr := .app p (.ident p "Err") [] false
      let tops := castTops env S sargs T (env.tvars.map (·.1))
      let chainE := tops.foldr (fun d acc =>
        let bound := s!"$castAs{p.line}_{p.col}_{D}_{d}"
        some (.ite p [.decl p bound none false (.app p (.ident p d) [.ident p obj] true)]
          (.app p (.ident p l.name) (.ident p bound :: (l.params.drop 1).map argOf) (l.specs.contains "decides")) acc))
        (if pre.isEmpty then elseE else some err)
      let some chainE := chainE | eerr p s!"no class is below both {rx.ty.show} and {T}, so {T}[…] would always fail"
      let expC : Option Ty ← if elseE.isNone then pure (some .void) else match exp, l.branchTy with
        | some t, _ => pure (some t)
        | none, some t => some <$> resolveTy env p t
        | none, none => pure none
      let rc ← elabE ctxO chainE expC
      if pre.isEmpty then return some rc
      let re ← elseOf
      let eE ← coerce p re rc.ty
      let cond := pre.foldr Expr.seq (.heap (.isTag (common.map env.tagOf)) [.local y])
      return some ⟨.ite cond rc.e eE, rc.ty⟩
    -- (then: the object in a slot, and one dispatch per set of pins)
    let (pre, y) ← match rx.e with
      | .local y => pure ([], y)
      | e => do
        let y ← fresh rx.ty
        pure ([Expr.assign y e], y)
    let re ← elseOf
    -- (the branch's own type, when the first elaboration took it; at
    -- another expected type, refused as it was there; with none, the
    -- `if`'s, as the first elaboration found it)
    let τ' : Ty ← match elseE, exp, l.branchTy with
      | none, _, _ => pure .void
      | some _, some t, some _ =>
        let ret ← resolveTy env p l.ret
        if ret != t.subst μT then eerr p s!"expected {t.show}, found {ret.show} (the branch of the cast to {shown})"
        pure t
      | some _, some t, none => pure t
      | some _, none, some t => resolveTy env p t
      | some ee, none, none => ifTy ee
    let eE ← coerce p re τ'
    let rargs := env.coreArgs S sargs
    let atR := rargs.zipIdx.map fun (r, j) => (pinArg j, r)
    let needOf (pins : List (Option Ty)) := (rargs.zip pins).filterMap fun (a, pin) => match pin with
      | some pt => let pt := pt.subst atR; if a == pt then none else some (a, pt)
      | none => none
    let mut parts : Array (List (Option Ty) × Array String) := #[]
    -- (keyed by each class's pins on the object's type arguments: the
    -- branch needs none of those a class below adds, so a test of classes
    -- that share those pins opens what the fewest of them add, as the
    -- checker's `openCount` does: none when one of them adds none; a cast
    -- that opens type arguments, #250, by all of each class's pins, as a
    -- method's dispatch is, since its tests open them)
    for d in common do
      -- (#351: through views, one test per class, each with its view and
      -- all of its pins, which the view relates to the object's)
      if env.viewed.contains S then parts := parts.push (env.corePins d, #[d]) else
      let k := if wide then env.dispatchPins d else (env.dispatchPins d).take rargs.length
      match parts.findIdx? (·.1 == k) with
      | some pi => parts := parts.modify pi fun (k', ds) => (k', ds.push d)
      | none => parts := parts.push (k, #[d])
    -- (an object that is no local: evaluated with a test of all the
    -- classes tested, in one condition, so that its effects roll back and
    -- its failure takes the else when the cast fails; the dispatch then
    -- tests each part, its end unreachable)
    let mut acc := if pre.isEmpty then eE else .prim .userErr []
    let mut tested : Array String := #[]
    for (pins, part) in parts.toList.reverse do
      -- (#250: the type arguments the test opens, as fresh parameters
      -- `$ext i`, which the refinement binds; the object is a `T` at the
      -- first of them)
      -- (each as comparable as the parameter it stands for: the target's,
      -- or past those, the tested class's own)
      -- (#351: through views, the object's are all fresh, as many as the
      -- class has, related to `X`'s by its view)
      let viewedS := env.viewed.contains S
      let dV := part[0]!
      let nV := (env.coreVars dV).length
      let extOf : List Ty := if viewedS then (List.range nV).map fun i => Ty.param s!"$ext{i}" false
        else if !wide then [] else
        (List.range (pins.length - rargs.length)).map fun i => Ty.param s!"$ext{i}" false
      let rxs := if viewedS then extOf else rargs ++ extOf
      let atX := rxs.zipIdx.map fun (r, j) => (pinArg j, r)
      let viewEqs : List (Ty × Ty) := if !viewedS then [] else rargs.zip (env.viewOf S dV extOf)
      let needX : List (Ty × Ty) := viewEqs ++ (rxs.zip pins).filterMap fun (a, pin) => match pin with
        | some pt => let pt := pt.subst atX; if a == pt then none else some (a, pt)
        | none => none
      if !VTy.pinsBelow (env.lowerPins pins) rxs.length then
        eerr p s!"cannot cast {withArticle rx.ty.show} to {shown} yet: class {part[0]!} relates its type arguments to ones that {S} does not have (#209, #243)"
      -- (no object of `part` can be this one: no test)
      let some μF := Ty.unifyEqs coreFields [] (if wide || viewedS then needX else needOf pins) | continue
      -- (the object as a `T`: its type parameters from the test's type
      -- arguments, refined)
      let dTyX ← if !wide && !viewedS then pure ((Ty.struct T targs).subst μF) else
        -- (a target seen through views has the tested class's view of it, #351)
        let rxsF := rxs.map (·.subst μF)
        match Ty.unifyEqs coreFields [] ((env.coreArgs T targs).zip
            (if env.viewed.contains T then env.viewOf T dV rxsF else rxsF)) with
        | some θD => pure ((Ty.struct T targs).subst θD)
        | none => eerr p s!"cannot cast {withArticle rx.ty.show} to {shown} yet: the object's type arguments as {withArticle part[0]!} do not determine {T}'s (#250)"
      let targetArgs := match dTyX with | .struct _ args => args | _ => []
      let some μF := env.refineComparable? μF (env.comparableArgs T targetArgs) | continue
      let dTyX := dTyX.subst μF
      let dL : Local := { name := D, slot := y, ty := dTyX, mutable := false }
      -- As for method dispatch, pass witnesses at the caller's own types.
      -- Pins may equate one to a newly opened component of a compound type.
      let unrefine := μF.filterMap fun (x, t) =>
        if ctx.dictVars.contains x && t.params.any (·.startsWith "$ext") then
          (ctx.types.tvars.lookup x).map (t, ·)
        else none
      let ctx' := { ctx with
        unrefine := unrefine ++ ctx.unrefine,
        locals := dL :: ctx.locals.map fun loc => { loc with ty := loc.ty.subst μF, storage := loc.storage.map (·.subst μF) },
        types := { env with tvars := env.tvars.map fun (m, t) => (m, t.subst μF) } }
      let argOf (sp : SParam) : SExpr :=
        if sp.typeValue && sp.name.startsWith "$type" then .app p (.ident p "$witness") [.ident p (sp.name.drop 5).toString] false
        else .ident p sp.name
      let rc ← elabApp ctx' p (.ident p l.name) (l.params.map argOf)
        (l.specs.contains "decides") (some (τ'.subst μF))
      -- (a suspends call carries the defers active at it, which go around
      -- the whole dispatch instead, as a method's, #243)
      let rcE : Expr := match rc.e with
        | .seq (.ite (.prim .fail []) _ (.lit .void)) b => b
        | e => e
      let .call fi (.local s0 :: es) := rcE
        | eerr p s!"cannot lift the branch of the cast to {shown} yet: its call is not a plain one (#243)"
      if s0 != y then eerr p s!"cannot lift the branch of the cast to {shown} yet (#243)"
      acc := .ite (.heap (.isTag (part.toList.map env.tagOf)) [.local y]) (.call fi (.local y :: es)) acc
      tested := part ++ tested
    let t ← fresh τ'
    -- (its value in a temporary at its type, as a suspends call's takes,
    -- and the defers active here around it when its function suspends)
    let mark (e : Expr) : EM Expr := if l.specs.contains "suspends" then withMark ctx e else pure e
    if pre.isEmpty then return some ⟨← mark (.assign t acc), τ'⟩
    let cond := pre.foldr Expr.seq (.heap (.isTag (tested.toList.map env.tagOf)) [.local y])
    return some ⟨← mark (.assign t (.ite cond acc eE)), τ'⟩

/-- (#243) Clause `c` with the cast at `q` inside it, which only a failure
    context's clause may be, lifted out to be one before it, as a choice
    there is (`Refine.markCast`, `Choice.liftClause`). `bound`: names the
    clauses before it bind, which are values too. -/
def liftCastClause (ctx : Ctx) (bound : List String) (q : Pos) (c : SExpr) : List SExpr :=
  Choice.liftClause (fun n => choiceValues ctx n || bound.contains n) (choiceField ctx) (Refine.markCast q c)
    (fieldOrder := choiceOrder ctx)

/-- (#243, #351) A failure context's clauses `cs`, then `after` (an `if`'s
    branch, a `for`'s body, a `first{…}`'s value), with a clause `D :=
    T[X]`, or `T[X]` of a class (past the first, if `later`), that only such
    a clause may be (one that refines type arguments, opens them, or goes
    through a view): `asWritten` first, and when that is refused for the
    cast at `k`, the context's own form for it, `alone k` (the `if`'s, when
    nothing before it needs undoing), else `rebuild` with the cast taking
    the clauses after it, up to the next generator (`isGen`), as its branch
    in a clause of its own, and `after` casting again
    (`Refine.castRestClauses`). Such a cast inside a clause is lifted out to
    be a clause of its own first (`liftCastClause`); one in an expression the
    failure context evaluates outside its clauses (`blocks`: an `if`'s
    branch, with the elaboration with it replaced) makes that expression the
    block of it (`Refine.castsOf`). `none` without a cast to a class. -/
def withCastClauses (ctx : Ctx) (cs : List SExpr) (after : SExpr) (isGen : SExpr → Bool) (asWritten : EM R)
    (rebuild : List SExpr → SExpr → EM R) (later : Bool := false)
    (alone : Nat → String → EM (Option R) := fun _ _ => pure none)
    (blocks : List (SExpr × (SExpr → EM R)) := []) : EM (Option R) := do
  -- (`D := T[X]` may be an index, `A[i]`: the one the refusal is at)
  let castAt : List (Nat × Pos) := cs.zipIdx.filterMap fun
    | (.decl _ _ none false (.app q (.ident _ _) [_] true), i) => if later && i == 0 then none else some (i, q)
    | (.app q (.ident _ T) [_] true, i) =>
      if (later && i == 0) || !ctx.types.classes.contains T then none else some (i, q)
    | _ => none
  let inner : List (Nat × Pos) := cs.zipIdx.flatMap fun (c, i) =>
    (Refine.castsIn ctx.types.classes.contains c).map (i, ·)
  let blockAt : List (Nat × Pos) := blocks.zipIdx.flatMap fun ((e, _), j) =>
    (Refine.castsOf ctx.types.classes.contains e).map (j, ·)
  if castAt.isEmpty && inner.isEmpty && blockAt.isEmpty then return none
  let st0 ← get
  match ← tryCatch (Except.ok <$> asWritten) (fun err => pure (Except.error err)) with
  | .ok r => return some r
  | .error err =>
    let some refusal := Refine.castRefusal? err | throw err
    if let some (e, elabWith) := (blockAt.find? (·.2 == refusal.pos)).bind fun (j, _) => blocks[j]? then
      set st0
      return some (← elabWith (.block e.pos [e]))
    if let some (k, _) := inner.find? (·.2 == refusal.pos) then
      set st0
      let lifted := liftCastClause ctx (Choice.boundIn (cs.take k)) refusal.pos cs[k]!
      return some (← rebuild (cs.take k ++ lifted ++ cs.drop (k + 1)) after)
    let some (k, _) := castAt.find? (·.2 == refusal.pos) | throw err
    let some cast := Refine.castClause? cs[k]! | throw err
    set st0
    if let some r ← alone k err then return some r
    let bound := Choice.boundIn cs
    let lift (c : SExpr) : List SExpr :=
      Choice.liftClause (fun n => choiceValues ctx n || bound.contains n) (choiceField ctx) c (fieldOrder := choiceOrder ctx)
    let moved (computed : Bool) := Refine.castRestClauses (cs.take k) cast refusal.opens (cs.drop (k + 1)) after
      isGen ctx.types.classes.contains (fun n => (ctx.lookup n).any (!·.mutable)) computed lift
      (fun f => !ctx.types.varFields.any (·.2 == f))
    let (cs', after', _, _) ← match moved false with
      | .ok r => pure r
      | .error why => throw s!"{err} ({why})"
    -- (a later cast of an object computed among the moved clauses is cast
    -- again from that object, bound first, when `after` needs it: when it
    -- is refused without)
    let st1 ← get
    match ← tryCatch (Except.ok <$> rebuild cs' after') (fun err => pure (Except.error err)) with
    | .ok r => return some r
    | .error err1 =>
      -- (#250: saying which later casts are not cast again, as their objects
      -- may name type arguments a cast opens and are no fields read from it)
      let err1 := match moved true with
        | .ok (_, _, _, e :: es) => s!"{err1} ({if es.isEmpty then s!"the cast that binds {e} is" else s!"the casts that bind {", ".intercalate (e :: es)} are"} not repeated where the clauses' names are used, as its object may name type arguments a cast before it opens and is not read from that cast's name by fields that are no vars (#250))"
        | _ => err1
      let .ok (cs'', after'', true, _) := moved true | throw err1
      set st1
      return some (← tryCatch (rebuild cs'' after'') fun _ => throw err1)

/-- Infer a producer's signature instance from its canonical arguments. -/
def loopInstanceOf (ctx : Ctx) (p : Pos) (sig : Sig) (types : List Ty) : EM (List (String × Ty)) := do
  let some σ := (sig.params.zip types).foldlM (fun σ (pt, t) => Ty.matchArg ctx.types σ pt t) []
    | eerr p s!"cannot infer the parameter instance of {sig.name}'s lazy generator (#283)"
  if let some (n, _) := sig.tparams.find? fun (n, _) => (σ.lookup n).isNone then
    eerr p s!"{sig.name}'s type parameter {n} is not determined by its arguments' types here (#235)"
  return σ

/-- Resolve a mutual member's private source aliases while keeping actual
    Core parameter names at their own identities, including permutations. -/
def loopMemberCtx (ctx : Ctx) (entry member : String) (σ : List (String × Ty)) : Ctx :=
  if entry == member then ctx else
  let aliases := σ.map fun (n, t) => (Choice.memberTypeName member n, t)
  let core := Ty.mergeParamBounds (σ.flatMap fun (_, t) => t.paramsC)
  let tvars := aliases ++ core.map (fun (n, cmp) => (n, Ty.param n cmp)) ++ ctx.types.tvars
  { ctx with types := { ctx.types with tvars } }

/-- A lazy invocation selects one leaf after running its path's prefixes.
    Leaf contexts retain branch bindings for saved continuation items. -/
structure LoopTailCode where
  select : Expr
  arms : Array (Ctx × List SExpr)
  itemCode : Expr
  next : Nat

partial def elabLoopTailWith (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (ctx : Ctx) (tail : SExpr) (k start : Nat) : EM LoopTailCode := do
  let vd : Expr := .lit .void
  let c := { ctx with canFail := true, inTaking := true }
  match tail with
  | .app _ (.ident _ "$returnTail") [.block p ss] false =>
    let (pre, value) := Choice.loopBlockParts p ss
    let (r, ca) ← elabSeq c pre none
    let code ← elabLoopTailWith elabSeq ca value k start
    return { code with select := .seq r.e code.select, itemCode := .seq r.e code.itemCode }
  | .ite _ cs t (some u) =>
    let (cond, ca) ← elabSeq c cs none
    let yes ← elabLoopTailWith elabSeq ca t k start
    let no ← elabLoopTailWith elabSeq ctx u k yes.next
    return { select := .ite cond.e yes.select no.select, arms := (yes.arms ++ no.arms),
             itemCode := .seq cond.e (.seq yes.itemCode no.itemCode), next := no.next }
  | value =>
    let alts := (Choice.alts? value).getD [value]
    return { select := .seq (.assign k (.lit (.int (start : Nat)))) vd,
             arms := #[(ctx, alts)], itemCode := vd, next := start + (alts.map Choice.flatCount).foldl (· + ·) 0 }

/-- (#283) A return frame of a lazily taken recursive group: the code after a
    choice point in an alternative, `$then(point, hole, code)`, which runs on
    each of the point's values, bound to `hole`; the point is a call of the
    group, or a choice, each of whose alternatives' values goes through it
    (a frame they share). `lives` are the names of the alternative's context
    (`ctx`) the code uses: their values when the frame is pushed are kept in
    it, on the continuation of the call's items. `pre`: the clauses that run
    before the call, with its arguments (what the alternative reads before
    the call that may not read the same after it, bound to names),
    elaborated once; `ctx` has their names. `member`: when the code reaches
    another choice point, a continuation member (`Choice.contOf?`), its
    index among the group's members. -/
structure LoopFrame where
  hole : String
  lives : List Local
  code : SExpr
  ctx : Ctx
  pre : Option Expr := none
  /-- Where the prefix sets a name, which the next alternative would see. -/
  preSet : Option Pos := none
  member : Option Nat := none
  /-- The hole's type, when not the group's result type: a choice's values'
      (`probeHoleWith`). -/
  inTy : Option Ty := none
  /-- The type of what the code gives, when not the group's result type:
      the hole's of the frame after it (a choice's frame its values go to). -/
  outTy : Option Ty := none

/-- (#283) The type of the values of a choice that go through its frame, when
    it is not the group's result type `rty` (they do not coerce to it): its
    first alternative's, a value's, or the code's after a call in it. None
    when that is a call of the group, whose values are at `rty`. -/
partial def probeHoleWith (elabE : Ctx → SExpr → Option Ty → EM R) (ca : Ctx) (rty : Ty) (cs : List SExpr) :
    EM (Option Ty) := do
  let st ← get
  let some (c, e) ← (match cs.head? with
    | some (.app _ (.ident _ "$rec") _ false) | some (.app _ (.ident _ "$recTo") _ false) => pure none
    | some (.app _ (.ident _ "$then") (p@(.app _ (.ident _ _) _ false) :: .ident _ h :: k :: _) false) =>
      if (Choice.contOf? k).isSome then pure none else do
      -- (the hole's type: a call's, the group's; a choice's or an `if`'s
      -- leaf's, #283, its first alternative's)
      let ht ← match Choice.alts? p, p with
        | some ps, _ => pure ((← probeHoleWith elabE ca rty ps).getD rty)
        | none, .app _ (.ident _ "$then") _ false => pure ((← probeHoleWith elabE ca rty [p]).getD rty)
        | none, _ => pure rty
      let hl : Local := { name := h, slot := ← fresh ht, ty := ht, mutable := false }
      pure (some ({ ca with locals := hl :: ca.locals }, k))
    | some a => pure (some (ca, a))
    | none => pure none) | set st; return none
  -- (a probe only: when the value does not elaborate apart, as a call's
  -- code that reads a name its prefix binds, the result type)
  let ty? ← tryCatch (do
      let r ← elabE { c with typeOnly := true, canFail := true, inTaking := true } e none
      let fits ← tryCatch (do let _ ← coerce e.pos r rty; pure true) (fun _ => pure false)
      pure (if fits then none else some r.ty))
    (fun _ => pure none)
  set st
  return ty?

/-- (#283) An alternative of a tail's leaf flattened (`Choice.flatCount`), with
    the frames it adds to `frames`, in order: a value or a call of the group,
    and the frames its values go through, innermost first. -/
partial def loopFlatWith (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx)) (rty : Ty)
    (ca : Ctx) (frames : Array LoopFrame) (a : SExpr) (outer : List Nat := []) :
    EM (Array LoopFrame × List (SExpr × List Nat)) := do
  let .app _ (.ident _ "$then") (c :: .ident _ h :: k :: rest) false := a | return (frames, [(a, outer)])
  let (pre, fc) ← match rest with
    | [.block _ ss] => do
      let (r, c) ← elabSeq { ca with canFail := true, inTaking := true } ss none
      pure (some r.e, { c with canFail := ca.canFail, inTaking := ca.inTaking })
    | _ => pure (none, ca)
  -- (#283) the frame of an `if` that is a point, in each of its leaves: one
  -- for all, made at its first, which has its code (`Choice.sameFrame`)
  if Choice.isSameFrame k then
    let some j := (List.range frames.size).reverse.find? (fun j => (frames[j]?.map (·.hole)) == some h)
      | eerr a.pos "internal: an if's leaf before its frame (#283)"
    return ← loopFlatNext elabE elabSeq rty ca frames c (j :: outer)
  let own := h :: Choice.localsOf k
  let preSet := rest.findSome? fun e => if Choice.anyE (fun | .set .. => true | _ => false) e then some e.pos else none
  let j := frames.size
  let lives := fc.captureEvidence ((Choice.namesUsed k).eraseDups.filterMap fun n =>
    if own.contains n then none else fc.lookup n) own
  let inTy ← match Choice.alts? c, c with
    | some cs, _ => probeHoleWith elabE ca rty cs
    | none, .app _ (.ident _ "$rec") _ false | none, .app _ (.ident _ "$recTo") _ false => pure none
    -- (a value entering a member, `Choice.enterOf`: its own type)
    | none, _ => probeHoleWith elabE ca rty [c]
  let outTy := (outer.head?.bind (frames[·]?)).bind (·.inTy)
  let frames := frames.push { hole := h, code := k, ctx := fc, pre, preSet, lives, inTy, outTy }
  loopFlatNext elabE elabSeq rty ca frames c (j :: outer)
where
  /-- The point `c` with the frames `fs`: a choice's alternatives each, a
      point with a frame of its own (an `if`'s leaf) flattened in turn, or
      the call or value itself. -/
  loopFlatNext (elabE : Ctx → SExpr → Option Ty → EM R)
      (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx)) (rty : Ty) (ca : Ctx)
      (frames : Array LoopFrame) (c : SExpr) (fs : List Nat) :
      EM (Array LoopFrame × List (SExpr × List Nat)) := do
    match Choice.alts? c, c with
    | some cs, _ =>
      cs.foldlM (fun (fr, acc) y => do
        let (fr, ys) ← loopFlatWith elabE elabSeq rty ca fr y fs
        pure (fr, acc ++ ys)) (frames, [])
    | none, .app _ (.ident _ "$then") _ false => loopFlatWith elabE elabSeq rty ca frames c fs
    | none, _ => return (frames, [(c, fs)])

/-- The return frames of a tail's alternatives, in the order of its arms. -/
def loopFramesWith (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx)) (rty : Ty)
    (arms : List (Ctx × List SExpr)) : EM (List LoopFrame) := do
  let mut out : Array LoopFrame := #[]
  for (ca, as) in arms do
    for a in as do
      out := (← loopFlatWith elabE elabSeq rty ca out a).1
  return out.toList

/-- The continuation `k` with frame `j` pushed on it, holding `vals`. -/
def framePush (ctx : Ctx) (lives : List (List Ty)) (j : Nat) (vals : List Expr) (k : Expr) : Expr :=
  let fr : Expr := .prim .mkTup (lives.zipIdx.map fun (_, i) =>
    if i == j then .prim .mkSome [if vals.isEmpty then .lit .void else .prim .mkTup vals] else .lit .none)
  .prim .mkSome [.heap (.new (ctx.types.tagOf "$lazycell")) [fr, k]]

/-- The value `leaf` given to the continuation `k` (#283): each frame's code
    in turn, innermost first, on the value the one before gave, with the
    frame's lives in slots of their own (the item's names stay as they are),
    until no frame is left. It runs where the value does, in the consumer's
    failure context, so what the frames do is undone with the value. A
    continuation member's frame runs that member's code instead,
    `memberArm j t v kk` (its lives in the tuple `t`, the value in `v`, the
    rest of the continuation in `kk`), which may leave the loop: the lazy
    loop's at the member's next choice point, and a function of its own's
    with that member's packet. `result v`: what the loop ends with, from the
    value `v` it came to (it alone, when no member left it). -/
def frameApplyWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (p : Pos)
    (frames : List LoopFrame) (rty : Ty) (k leaf : Expr)
    (memberArm : Nat → Nat → (Option Ty → Nat) → Nat → EM Expr := fun _ _ _ _ => pure (.lit .void))
    (result : Nat → Expr := Expr.local)
    (leafAt : Option ((Option Ty → Nat) → Expr) := none) (leafTys : List Ty := []) : EM Expr := do
  let vd : Expr := .lit .void
  let lives := frames.map fun f => f.lives.map (·.ty)
  let fty := frameTy lives
  let cellTy : Ty := .struct "$lazycell" [fty]
  let cfs := ctx.types.fields "$lazycell" [fty]
  let (some (itemF, _), some (nextF, _)) := (fieldIndex cfs "$LItem", fieldIndex cfs "$LNext")
    | eerr p "internal: the frames of a $loop (#283)"
  let v ← fresh rty
  let kk ← fresh (frameContTy lives)
  let cell ← fresh cellTy
  let fr ← fresh fty
  -- (#283) a value slot of each other type a frame's hole or code has (a
  -- choice's frame's), `v` the group's result type's
  let mut tys : List Ty := []
  for t in leafTys ++ frames.flatMap (fun f => f.inTy.toList ++ f.outTy.toList) do
    if !tys.contains t then tys := tys ++ [t]
  let mut typed : List (Ty × Nat) := []
  for t in tys do typed := typed ++ [(t, ← fresh t)]
  let slotOf (t : Option Ty) : Nat := match t with
    | some ty => ((typed.find? (·.1 == ty)).map (·.2)).getD v
    | none => v
  let mut arms : List (Nat × Nat × Expr) := []
  for (f, j) in frames.zipIdx do
    let t ← fresh (frameLivesTy (f.lives.map (·.ty)))
    if f.member.isSome then
      arms := arms ++ [(j, t, ← memberArm j t slotOf kk)]
      continue
    let ls ← f.lives.mapM fun l => do return { l with slot := ← fresh l.ty }
    let (inTy, outTy) := (f.inTy.getD rty, f.outTy.getD rty)
    let h ← fresh inTy
    let hole : Local := { name := f.hole, slot := h, ty := inTy, mutable := false }
    let c : Ctx := { f.ctx with canFail := true, inTaking := true, locals := hole :: ls.reverse ++ f.ctx.locals }
    let r ← elabE c f.code (some outTy)
    let e ← coerce f.code.pos r outTy
    let unpack := ls.zipIdx.foldr (fun (l, i) acc => Expr.seq (.assign l.slot (.prim (.tupGet i) [.local t])) acc) vd
    arms := arms ++ [(j, t, .seq unpack (.seq (.assign h (.local (slotOf f.inTy))) (.seq (.assign (slotOf f.outTy) e) vd)))]
  let dispatch : Expr := arms.foldr (fun (j, t, body) acc =>
    .ite (.assign t (.prim .query [.prim (.tupGet j) [.local fr]])) body acc) vd
  let step : Expr := .ite (.assign cell (.prim .query [.local kk]))
    (.seq (.assign fr (.heap (.get itemF) [.local cell])) (.seq (.assign kk (.heap (.get nextF) [.local cell])) dispatch))
    Expr.brkV
  -- (a leaf of a type of its own sets that type's slot itself)
  let start : Expr := match leafAt with
    | some code => code slotOf
    | none => .assign v leaf
  return .seq start (.seq (.assign kk k) (.seq (.loop step) (result v)))

/-- (#283) `elabLoopGen` for a strongly connected group of functions with
    several values, taken lazily (`$group(tail, $member(H, params, clauses,
    r := tail)…)` in the marker): one stack of items `(k, every member's
    parameters and names…)`, `k` the alternative to run, numbered across
    the members, or `-1 - i` to start member `i` (its clauses, then its
    branch). A call of a member, `$rec` (its own) or `$recTo(H, …)`, pushes
    the item that starts that member, its parameters from the arguments.
    Otherwise as `elabLoopGen`. Defined before the mutual block, with the
    block's functions it calls as arguments (#325). -/
partial def elabLoopGenGroupWith (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (ctx : Ctx) (p : Pos) (g : String) (ps cls : List SExpr) (_rsty : STy) (tail0 : SExpr)
    (members : List SExpr) : EM LoopGen := do
  let vd : Expr := .lit .void
  let args ← ps.mapM fun
    | .ident q n => match ctx.lookup n with
      | some l => pure l
      | none => eerr q s!"internal: parameter {n} of a $loop (#246)"
    | e => eerr e.pos "internal: a $loop parameter (#246)"
  let some entry := ctx.sig? g | eerr p s!"internal: no signature for {g} (#283)"
  let σ ← loopInstanceOf ctx p entry (args.map (·.ty))
  let rty := entry.ret.subst σ
  let templates ← members.mapM fun
    | .app _ (.ident _ "$member") [.ident _ h, .block _ hps, .block _ hcls, .decl _ _ _ _ htail] false =>
      pure (h, hps, hcls, htail)
    | _ => eerr p "internal: a $member (#283)"
  let templates := (g, ps, cls, tail0) :: templates
  let mut instances := [(g, σ)]
  for (h, _, _, _) in templates.drop 1 do
    if let some sig := (ctx.sig? h).filter (·.tparams.isEmpty) then
      instances := instances ++ [(sig.name, [])]
  -- Discover each generic member at the actual calls reaching it. This
  -- uses ordinary tuple/named/default binding and result-type inference,
  -- in an isolated probe whose slots, effects and helper requests are reset.
  -- Later edges are checked against the established instance when lowered,
  -- just as self-recursive lazy calls keep their invocation's parameter types.
  if instances.length < templates.length then
    let mut todo := instances.map (·.1)
    let mut errors : List (String × String) := []
    while !todo.isEmpty do
      let h := todo.head!
      todo := todo.tail!
      let some (_, hps, hcls, htail) := templates.find? (·.1 == h)
        | eerr p "internal: a mutual generator template"
      let some sig := ctx.sig? h | eerr p s!"internal: no signature for {h} (#283)"
      let saved ← get
      let ts := sig.params.map (·.subst ((instances.lookup h).getD []))
      let pls ← (hps.zip ts).mapM fun
        | (.ident _ n, t) => do return ({ name := n, slot := ← fresh t, ty := t, mutable := false } : Local)
        | _ => eerr p "internal: a $member parameter (#283)"
      let c := loopMemberCtx ctx g h ((instances.lookup h).getD [])
      let c := { c with locals := pls.reverse ++ c.locals, typeOnly := true, canFail := true, inTaking := true }
      let (_, cc) ← elabSeq c hcls none
      let probeK ← fresh .int
      let code ← elabLoopTailWith elabSeq cc htail probeK 0
      -- (each alternative in its leaf's context; #283, a choice's own too,
      -- and those of a continuation member's code, where its frame is
      -- pushed, so a member reached only from it is found)
      let mut work : List (Ctx × SExpr) := code.arms.toList.flatMap fun (ca, alts) => alts.map (ca, ·)
      while true do
        let (ca, alt) :: more := work | break
        work := more
        if let .app _ (.ident _ "$then") (pt :: .ident _ hn :: k :: rest) false := alt then
          if let some cs := Choice.alts? pt then work := cs.map (ca, ·) ++ work
          -- (an `if`'s leaf with a frame of its own)
          if let .app _ (.ident _ "$then") _ false := pt then work := (ca, pt) :: work
          if let some (ccls, ctail) := Choice.contOf? k then
            let cf ← match rest with
              | [.block _ ss] => do pure (← elabSeq ca ss none).2
              | _ => pure ca
            let hty := (← match Choice.alts? pt, pt with
              | some cs, _ => probeHoleWith elabE ca rty cs
              | none, .app _ (.ident _ "$rec") _ false | none, .app _ (.ident _ "$recTo") _ false => pure none
              | none, _ => probeHoleWith elabE ca rty [pt]).getD rty
            let hl : Local := { name := hn, slot := ← fresh hty, ty := hty, mutable := false }
            let (_, cm) ← elabSeq { cf with locals := hl :: cf.locals } ccls none
            let mcode ← elabLoopTailWith elabSeq cm ctail probeK 0
            work := work ++ mcode.arms.toList.flatMap fun (ca2, alts2) => alts2.map (ca2, ·)
        let alt := match alt with
          | .app _ (.ident _ "$then") (c :: _) false => c
          | a => a
        let call := match alt with
          | .app q (.ident _ "$rec") as false => some (q, h, as)
          | .app q (.ident _ "$recTo") (.ident _ target :: as) false => some (q, target, as)
          | _ => none
        if let some (q, target, as) := call then
          if (instances.lookup target).isSome then continue
          let some targetSig := ctx.sig? target | eerr q s!"internal: no signature for {target} (#283)"
          let attempt ← tryCatch (do
            let packet ← elabE { ca with callInstanceProbe := some target }
              (.app q (.ident q target) as targetSig.decides) (some rty)
            let .tup types := packet.ty | eerr q "internal: a mutual argument type packet"
            pure (Except.ok ((targetSig.tparams.map (·.1)).zip types))) (fun err => pure (.error err))
          match attempt with
          | .ok σ =>
            instances := instances ++ [(target, σ)]
            todo := todo ++ [target]
          | .error err => errors := errors ++ [(target, err)]
      restoreConstructProbe ctx saved
    for (h, _, _, _) in templates do
      if (instances.lookup h).isNone then
        throw ((errors.lookup h).getD s!"cannot infer {h}'s mutual generator instance (#283)")
  -- (the members: the called one first, its parameters' slots its own)
  let mut ms : Array (String × List Local × List SExpr × SExpr) := #[]
  let pls0 ← args.mapM fun l => do return { l with slot := ← fresh l.ty }
  ms := ms.push (g, pls0, cls, tail0)
  for m in members do
    let .app _ (.ident _ "$member") [.ident _ h, .block _ hps, .block _ hcls, .decl _ _ _ _ htail] false := m
      | eerr p "internal: a $member (#283)"
    let some sig := ctx.sig? h | eerr p s!"internal: no signature for {h} (#283)"
    if hps.length != sig.params.length then eerr p s!"internal: the parameters of {h} (#283)"
    let hpls ← (hps.zip (sig.params.map (·.subst ((instances.lookup h).getD [])))).mapM fun (e, t) => match e with
      | .ident _ n => do return ({ name := n, slot := ← fresh t, ty := t, mutable := false } : Local)
      | _ => eerr p "internal: a $member parameter (#283)"
    ms := ms.push (h, hpls, hcls, htail)
  let names := ms.toList.map (·.1)
  -- (each member's clauses, then its branches' conditions, in its own
  -- context; the names each saves in an item: its parameters, then the others)
  let k ← fresh .int
  let mut infos : Array (R × LoopTailCode × List Local) := #[]
  for (h, pls, mcls, mtail) in ms do
    let c := loopMemberCtx ctx g h ((instances.lookup h).getD [])
    let lctx : Ctx := { c with locals := pls.reverse ++ c.locals }
    let newOf (c : Ctx) : List Local := c.locals.take (c.locals.length - lctx.locals.length)
    let (rc, cc) ← elabSeq { lctx with canFail := true, inTaking := true } mcls none
    let code ← elabLoopTailWith elabSeq cc mtail k 0
    let mut tls : List Local := pls
    for l in (newOf cc ++ code.arms.toList.flatMap fun (ca, _) => newOf ca).reverse do
      if !tls.any (·.slot == l.slot) then tls := tls ++ [l]
    infos := infos.push (rc, code, tls)
  -- (#283) the return frames of the alternatives, each alternative flattened
  -- (a choice's shared frame on each of its alternatives, `loopFlatWith`),
  -- and the continuation they are pushed on, which every item keeps, after
  -- every member's names. A frame whose code reaches another choice point
  -- is a continuation member's: the member, after the group's functions,
  -- its parameters the hole and the lives, its code elaborated where the
  -- frame is pushed; its alternatives may have frames again.
  let nSrc := infos.size
  let km? : Option Nat ← if ms.toList.any (fun (_, _, _, t) => Choice.hasContinuation t) then
      some <$> fresh .int else pure none
  let mut frameArr : Array LoopFrame := #[]
  let mut flats : Array (List (List (SExpr × List Nat))) := #[]
  -- (the function each member's code is of: its `$rec` calls that one)
  let mut origin : Array Nat := (List.range nSrc).toArray
  -- (the type of each member's values, when not the group's result type: a
  -- continuation member's that a choice's frame takes)
  let mut outs : Array (Option Ty) := (List.replicate nSrc none).toArray
  let mut mi := 0
  while mi < infos.size do
    let some (_, mcode, _) := infos[mi]? | break
    let mut armFlats : List (List (SExpr × List Nat)) := []
    for (ca, as) in mcode.arms do
      let mut fl : List (SExpr × List Nat) := []
      for a in as do
        let n0 := frameArr.size
        let (fr, xs) ← loopFlatWith elabE elabSeq rty ca frameArr a
        frameArr := fr
        fl := fl ++ xs
        for j in [n0:frameArr.size] do
          let some f := frameArr[j]? | continue
          let some (ccls, ctail) := Choice.contOf? f.code | continue
          let some kms := km? | eerr p "internal: a continuation member (#283)"
          -- (its hole at its choice's values' type; its values at the type
          -- the frame after it takes, `outs`)
          let hty := f.inTy.getD rty
          let hl : Local := { name := f.hole, slot := ← fresh hty, ty := hty, mutable := false }
          let ls ← f.lives.mapM fun l => do return { l with slot := ← fresh l.ty }
          let lctx : Ctx := { f.ctx with locals := hl :: ls.reverse ++ f.ctx.locals }
          let newOf (c : Ctx) : List Local := c.locals.take (c.locals.length - lctx.locals.length)
          let (rc, cc) ← elabSeq { lctx with canFail := true, inTaking := true } ccls none
          let code ← elabLoopTailWith elabSeq cc ctail kms 0
          let mut tls : List Local := hl :: ls
          for l in (newOf cc ++ code.arms.toList.flatMap fun (ca, _) => newOf ca).reverse do
            if !tls.any (·.slot == l.slot) then tls := tls ++ [l]
          frameArr := frameArr.set! j { f with member := some infos.size }
          infos := infos.push (rc, code, tls)
          origin := origin.push (origin.getD mi 0)
          outs := outs.push f.outTy
      armFlats := armFlats ++ [fl]
    flats := flats.push armFlats
    mi := mi + 1
  let frames := frameArr.toList
  let lives := frames.map fun f => f.lives.map (·.ty)
  let kl? : Option Local ← if frames.isEmpty then pure none else do
    let kTy := frameContTy lives
    pure (some { name := "$K", slot := ← fresh kTy, ty := kTy, mutable := false })
  -- (one item for all: every member's names, the members in order)
  let all : List Local := infos.toList.flatMap (·.2.2) ++ kl?.toList
  let bases : List Nat := (infos.toList.foldl (fun (acc, n) (_, _, tls) => (acc ++ [n], n + tls.length)) ([], 0)).1
  let tupTy : Ty := .tup (.int :: all.map (·.ty))
  let cellTy : Ty := .struct "$lazycell" [tupTy]
  let cfs := ctx.types.fields "$lazycell" [tupTy]
  let (some (itemF, _), some (nextF, _)) := (fieldIndex cfs "$LItem", fieldIndex cfs "$LNext")
    | eerr p "internal: the stack cells of a $loop (#246)"
  let w ← fresh (.opt cellTy)
  let cell ← fresh cellTy
  let sp ← fresh .int
  let it ← fresh tupTy
  let has ← fresh .logic
  let nx ← fresh .int
  -- (#283) with continuation members: the flag a value sets at a member's
  -- choice point, and the item that resumes there, which `after` pushes
  let bnd? : Option Nat ← km?.mapM fun _ => fresh .logic
  let stash? : Option Nat ← km?.mapM fun _ => fresh (.opt tupTy)
  let item (kE : Expr) (vals : List Expr) : Expr := .prim .mkTup (kE :: vals)
  let cur : List Expr := all.map (Expr.local ·.slot)
  let push (e : Expr) : Expr :=
    .seq (.assign cell (.heap (.new (ctx.types.tagOf "$lazycell")) [e, .local w]))
      (.seq (.assign w (.prim .mkSome [.local cell]))
        (.seq (.assign sp (p2 .add (.local sp) (.lit (.int 1)))) vd))
  -- (the item that starts member `j`, its parameters from `ts`; with a
  -- return frame, on the continuation `kE`)
  let startOf (j : Nat) (ts : List Nat) (kE : Option Expr := none) : Expr :=
    let b := bases.getD j 0
    let vals := cur.take b ++ ts.map Expr.local ++ cur.drop (b + ts.length)
    item (.lit (.int (-1 - (j : Int)))) (match kE with | some e => vals.dropLast ++ [e] | none => vals)
  -- (the continuation `base` with the frames `fs` pushed, innermost on top)
  let pushAll (fs : List Nat) (base : Expr) : Expr := fs.foldr (fun j acc =>
    framePush ctx lives j (((frames[j]?).map (·.lives)).getD [] |>.map (Expr.local ·.slot)) acc) base
  -- (an alternative of member `i` in its leaf's context `ca`, with its frames
  -- `fs`: its own frame's prefix, if any, before its arguments, in whose
  -- context they are; and, a call of the group's function, the callee, the
  -- arguments and where; a `$rec` of a continuation member is of the
  -- function whose code it is)
  let altOf (i : Nat) (ca : Ctx) (fs : List Nat) (a : SExpr) :
      Ctx × Option LoopFrame × Option (Nat × List SExpr × Pos) :=
    let fr? := fs.head?.bind (frames[·]?)
    let actx : Ctx := match fr?.bind (·.pre), fr? with
      | some _, some f => { f.ctx with canFail := true, inTaking := true }
      | _, _ => { ca with canFail := true, inTaking := true }
    (actx, fr?, match a with
      | .app q (.ident _ "$rec") args' false => some (origin.getD i 0, args', q)
      | .app q (.ident _ "$recTo") (.ident _ h :: args') false => (names.idxOf? h).map (·, args', q)
      | _ => none)
  -- (that call's arguments set into slots of their own for its parameters,
  -- after the prefix)
  let argsOf (actx : Ctx) (fr? : Option LoopFrame) (jm : Nat) (args' : List SExpr) (q : Pos) :
      EM (List Nat × Expr) := do
    let some (h, hpls, _, _) := ms[jm]? | eerr q "internal: a call in a group (#283)"
    let ts ← hpls.mapM fun l => fresh l.ty
    let assigns ← elabLoopArgsWith elabE actx q h args' hpls ts ((instances.lookup h).getD [])
    return (ts, match fr?.bind (·.pre) with | some e => Expr.seq e assigns | none => assigns)
  -- (the alternatives, numbered across the members' branches)
  let mut offs : Array Nat := #[]
  let mut total : Nat := 0
  for (_, armCode, _) in infos do
    offs := offs.push total
    total := total + armCode.next
  -- (each alternative's code by its number: a continuation member's leaf of
  -- one alternative has none here)
  let mut alts : Array (Nat × Expr) := #[]
  let mut values : Array (Nat × Option Ty × Expr) := #[]
  let mut kInits : Array (Nat × Expr) := #[]
  -- (#283) the type of a value of member `i` going to the frames `fs`: the
  -- hole's of the first, else the member's own, when not the result type
  let valueTy (i : Nat) (fs : List Nat) : Option Ty := match fs.head? with
    | some j => (frames[j]?).bind (·.inTy)
    | none => outs.getD i none
  let mut itemCode : Expr := vd
  let mut argSet : Option Pos := none
  let mut starts : Array Expr := #[]
  for ((rc, armCode, _), i) in infos.toList.zipIdx do
    let off := offs.getD i 0
    let isFn := i < nSrc
    if isFn then
      itemCode := .seq itemCode (.seq rc.e armCode.itemCode)
      let select := .seq armCode.select (.assign k (p2 .add (.local k) (.lit (.int (off : Nat)))))
      starts := starts.push (.ite (.seq rc.e select) vd (.seq (.assign k (.lit (.int (total : Nat)))) vd))
    let armFlats := flats.getD i []
    let firsts : List Nat := (armFlats.foldl (fun (acc, n) fl => (acc ++ [n], n + fl.length)) ([], off)).1
    for (((ca, _), fl), first) in (armCode.arms.toList.zip armFlats).zip firsts do
      -- (a continuation member's leaf with one alternative runs where the
      -- member's code does, in its frame's application, `memberArm`)
      let inline := !isFn && fl.length == 1
      for ((a, fs), j) in fl.zipIdx do
        let gi := first + j
        let next? : Option Nat := if j + 1 < fl.length then some (gi + 1) else none
        let cont : Expr := match next? with
          | some n => push (item (.lit (.int (n : Nat))) cur)
          | none => vd
        let (actx, fr?, call?) := altOf i ca fs a
        match call? with
        | some (jm, args', q) =>
          if argSet.isNone then
            argSet := args'.findSome? fun a' =>
              if Choice.anyE (fun | .set .. => true | _ => false) a' then some a'.pos else none
          if argSet.isNone then argSet := fr?.bind (·.preSet)
          if inline then continue
          let (ts, assigns) ← argsOf actx fr? jm args' q
          itemCode := .seq itemCode assigns
          let kE := kl?.bind fun kl => if fs.isEmpty then none else some (pushAll fs (.local kl.slot))
          alts := alts.push (gi, .ite assigns (.seq cont (push (startOf jm ts kE))) cont)
        | none =>
          if inline then continue
          let vty := valueTy i fs
          let r ← elabE actx a (some (vty.getD rty))
          values := values.push (gi, vty, ← coerce a.pos r (vty.getD rty))
          if let some kl := kl? then
            if !fs.isEmpty then kInits := kInits.push (gi, pushAll fs (.local kl.slot))
          let nextK : Int := match next? with | some n => (n : Int) | none => -1
          alts := alts.push (gi, .seq (.assign nx (.lit (.int nextK))) (.seq (.assign has (.lit (.logic true))) vd))
  -- (#283) a continuation member's code where its frame is applied to the
  -- value `v` (its lives in the tuple `t`, the rest of the continuation in
  -- `kk`): its clauses and branch, then a leaf of one alternative there, a
  -- value given to the frames after it or a call whose item it leaves, or,
  -- at a choice, the item of its first alternative: both a choice point,
  -- where the value's code stops (`bnd`)
  let memberArm (fj t : Nat) (slotOf : Option Ty → Nat) (kk : Nat) : EM Expr := do
    let some f := frames[fj]? | eerr p "internal: a continuation member's frame (#283)"
    let (some mi, some kms, some b, some st) := (f.member, km?, bnd?, stash?)
      | eerr p "internal: a continuation member (#283)"
    let some (rc, mcode, tls) := infos[mi]? | eerr p "internal: a continuation member (#283)"
    let hl :: ls := tls.take (1 + f.lives.length) | eerr p "internal: a continuation member's parameters (#283)"
    let off := offs.getD mi 0
    let armFlats := flats.getD mi []
    -- (the member's names are its items' too: kept before and given back
    -- after, so an item of the same member being taken keeps its own, which
    -- `after` pushes the next alternative with)
    let saved ← fresh (.tup (tls.map (·.ty)))
    let restore : Expr := tls.zipIdx.foldr (fun (l, i) acc =>
      .seq (.assign l.slot (.prim (.tupGet i) [.local saved])) acc) vd
    let stop (it : Expr) : Expr :=
      .seq (.assign st (.prim .mkSome [it])) (.seq restore (.seq (.assign b (.lit (.logic true))) Expr.brkV))
    let mut leaves : List (Nat × Expr) := []
    let mut lf : Nat := 0
    for ((ca, _), fl) in mcode.arms.toList.zip armFlats do
      let code ← match fl with
        | [(a, fs)] => do
          let (actx, fr?, call?) := altOf mi ca fs a
          match call? with
          | some (jm, args', q) =>
            let (ts, assigns) ← argsOf actx fr? jm args' q
            pure (Expr.seq assigns (stop (startOf jm ts (some (pushAll fs (.local kk))))))
          | none =>
            let vty := valueTy mi fs
            let r ← elabE actx a (some (vty.getD rty))
            let e ← coerce a.pos r (vty.getD rty)
            pure (Expr.seq (.assign (slotOf vty) e) (.seq (.assign kk (pushAll fs (.local kk))) restore))
        | _ => pure (stop (item (.lit (.int ((off + lf : Nat) : Int))) (cur.dropLast ++ [.local kk])))
      leaves := leaves ++ [(lf, code)]
      lf := lf + fl.length
    let dispatch : Expr := leaves.foldr (fun (i, c) acc =>
      .ite (p2 .eq (.local kms) (.lit (.int (i : Nat)))) c acc) vd
    let unpack := ls.zipIdx.foldr (fun (l, i) acc => Expr.seq (.assign l.slot (.prim (.tupGet i) [.local t])) acc) vd
    return .seq (.assign saved (.prim .mkTup (tls.map (Expr.local ·.slot))))
      (.seq unpack (.seq (.assign hl.slot (.local (slotOf f.inTy))) (.seq rc.e (.seq mcode.select dispatch))))
  let dispatch : Expr := alts.toList.foldr (fun (i, a) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) a acc) vd
  let unpack : Expr := (all.zipIdx).foldr (fun (l, j) acc =>
    .seq (.assign l.slot (.prim (.tupGet (j + 1)) [.local it])) acc) vd
  let init : Expr := .seq (.assign w (.lit .none)) (.seq (.assign sp (.lit (.int 0)))
    (push (item (.lit (.int (-1))) (args.map (Expr.local ·.slot) ++ cur.drop pls0.length))))
  let init : Expr := match kl? with
    | some kl => .seq (.assign kl.slot (.lit .none)) init
    | none => init
  let init : Expr := match stash? with
    | some st => .seq (.assign st (.lit .none)) init
    | none => init
  let start : Expr := (starts.toList.zipIdx).foldr (fun (st, i) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (-1 - (i : Int))))) st acc) vd
  let step : Expr := Expr.seq (.assign sp (p2 .sub (.local sp) (.lit (.int 1))))
    (.seq (.ite (.assign cell (.prim .query [.local w]))
        (.seq (.assign it (.heap (.get itemF) [.local cell])) (.seq (.assign w (.heap (.get nextF) [.local cell])) vd)) vd)
    (.seq (.assign k (.prim (.tupGet 0) [.local it]))
    (.seq unpack
    (.seq (.assign has (.lit (.logic false)))
    (.seq (.ite (p2 .lt (.local k) (.lit (.int 0))) start vd)
      dispatch)))))
  let value : Expr := values.toList.foldr (fun (i, _, e) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) e acc) (.prim .fail [])
  -- (#283) a value of a type of its own, for a choice's frame, set into its
  -- type's slot
  let leafTys : List Ty := values.toList.filterMap (·.2.1)
  let leafAt : Option ((Option Ty → Nat) → Expr) := if leafTys.isEmpty then none else
    some fun slotOf => values.toList.foldr (fun (i, t, e) acc =>
      .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) (.seq (.assign (slotOf t) e) vd) acc) (.prim .fail [])
  -- (#283) given to the frames of the item's continuation, with those of
  -- the value's own alternative, if any, on top
  let value ← match kl? with
    | some kl =>
      let k0 : Expr := kInits.toList.foldr (fun (i, e) acc =>
        .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) e acc) (.local kl.slot)
      -- (when a value came to a member's choice point: out of the
      -- consumer's failure context, which keeps what it did)
      frameApplyWith elabE ctx p frames rty k0 value memberArm (fun v => match bnd? with
        | some b => .ite (.prim .query [.local b]) (.seq .brk (.prim .userErr [])) (.local v)
        | none => .local v) leafAt leafTys
    | none => pure value
  -- (#283) what a value runs where it may come to a member's choice point
  -- runs once for all the values after it there, as clauses do
  if km?.isSome then itemCode := .seq itemCode value
  let after : Expr := .ite (p2 .ge (.local nx) (.lit (.int 0))) (push (item (.local nx) cur)) vd
  -- (and, after a value that came to a member's choice point, the item that
  -- resumes there, above the next alternative's, so values keep their order)
  let after ← match stash? with
    | some st => do
      let r ← fresh tupTy
      pure (Expr.seq after (.ite (.assign r (.prim .query [.local st]))
        (.seq (.assign st (.lit .none)) (push (.local r))) vd))
    | none => pure after
  return { init, step, sp, has, value, after, vty := rty, itemCode, argSet, instances, bnd := bnd?,
           frames := frames.map (fun f => (f.hole, f.lives.map (·.name), f.code)),
           frameTys := frames.map (fun f => (f.inTy, f.outTy)), kTy := kl?.map (·.ty) }

/-- Check a construction's value choices at the field's expected type.
    Keeping the original inline/lazy templates visits nested constructions
    under their real parameter aliases, rather than replacing them by calls. -/
def constructFieldsForTypes : SExpr → SExpr
  | .decl p f t v x =>
    .decl p f t v (if Choice.hasLiftable x then
      .app x.pos (.ident x.pos "$constructValuesType") [x] false else x)
  | e => e

end OpenVerse.Front
