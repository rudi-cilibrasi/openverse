/- Elaboration control; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.For
import OpenVerse.Front.Elab.Calls

namespace OpenVerse.Front
open OpenVerse
partial def elabSetWith (elabE : Ctx → SExpr → Option Ty → EM R) (elabMember : Ctx → Pos → R → String → EM R)
    (ctx : Ctx) (p : Pos) (lhs0 : SExpr) (op : Option String) (rhs0 : SExpr) : EM R := do
  if let .app _ (.ident _ "$refineCopyOut") [rhs] false := rhs0 then
    let r ← elabSetWith elabE elabMember ctx p lhs0 op rhs
    match r.e with
    | .assign target (.local result) =>
      modify fun st => { st with frameCopies := st.frameCopies ++ [{ target, result }] }
    | .assign target (.prim (.tupGet field) [.local result]) =>
      modify fun st => { st with frameCopies := st.frameCopies ++ [{ target, result, field := some field }] }
    | _ => eerr p "internal error: a refining copy-out is not a saved result"
    return r
  -- (`$withOld(O, R)`: for `op=`, the old value was read into `O` before
  -- the code that computes `R`, as `set` evaluates, #208)
  let (rhs, oldIn) : SExpr × Option Expr := match rhs0 with
    | .app _ (.ident _ "$withOld") [.ident _ o, r] false => (r, (ctx.lookup o).map (fun l => Expr.local l.slot))
    | r => (r, none)
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
  if let some (root, steps) := path lhs then if general steps then
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
    for (sp, f?, k?) in steps do
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
    -- a value of a class with no instance cannot exist, so the set is
    -- unreachable once the path reaches one; but the steps before it (the
    -- indices and keys, then the containers read) may fail first (#104)
    if let some ke := (List.range steps.length).find? fun k =>
        match tysA[k]! with | .struct sn _ => ctx.types.isEmptyClass sn | _ => false then
      let stepsA := steps.toArray
      let mut c := l.slot
      for k in [0:ke] do
        let (_, f?, _) := stepsA[k]!
        let c' ← fresh tysA[k + 1]!
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
      levels := levels.push (cur, tys[k]!, sp, f?, keys[k]!)
      if k == rhsAfter then
        -- `set P op= e` reads P before e, as the direct form does (Book of
        -- Verse: `set X += e` is `set X = X + e`; #58): the rest of the path,
        -- read now, gives the old leaf (it fails as `P` would, and is read
        -- again for the rebuild below)
        if op.isSome then
          let mut c2 := cur
          for k2 in [k:stepsA.size] do
            let (_, f2, _) := stepsA[k2]!
            let t2 := if k2 + 1 < stepsA.size then tys[k2 + 1]! else leafTy
            let c3 ← fresh t2
            pre := pre.push (.assign c3 (← readStep c2 tys[k2]! f2 keys[k2]!))
            c2 := c3
          oldLeaf := some c2
        let r ← rhsAt leafTy
        let tr ← fresh r.ty
        pre := pre.push (.assign tr r.e)
        rhsVal := some ⟨.local tr, r.ty⟩
      if k + 1 < stepsA.size then
        let c ← fresh tys[k + 1]!
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
        let old ← match oldLeaf with
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
    types. `none` when the cast does not refine: the plain path. -/
partial def elabRefinedIfWith (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (elabE : Ctx → SExpr → Option Ty → EM R) (withMark : Ctx → Expr → EM Expr) (ctx : Ctx) (p _dp : Pos) (D T : String) (x : SExpr) (body0 : SExpr)
    (elseE : Option SExpr) (exp : Option Ty) (made : Bool := false)
    (escRet : Option (Ty × Refine.Exits) := none)
    (outsideWrites : List Nat := []) :
    EM (Option R) := do
  let ctx := ctx.choiceCoercionScope
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
  -- (the locals the branch uses, in order of first use)
  let caps : List Local := (Choice.namesUsed body).filterMap fun n =>
    if n == D then none else ctx.locals.find? (·.name == n)
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
          let τ? ← tryCatch (do pure (some (← elabE { ctx with typeOnly := true } ee none).ty)) fun _ => pure none
          -- (an `else` that gives no value tells no type: the branch's own,
          -- under the refinement, when it ends, as the first elaboration
          -- finds it, if code outside it can name it)
          let own? ← if τ? != some .never then pure none else
            tryCatch (do
              let τ := (← elabE { refined (← fresh dTy) with typeOnly := true } (Refine.exitsAsErr body) none).ty
              pure (if opened.any (fun (n, _, _) => τ.params.contains n) then none else some τ)) fun _ => pure none
          let τ? := own?.orElse fun _ => τ?
          set st
          if !escapes then
            -- Discard a statement's value before building the copy-out tuple.
            pure (some (if τ?.any (· == .void) then .none else .raw (own?.map Ty.toSTy)))
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
  let tag := refineTagOf ctx
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
    let ctxB : Ctx := { refined dslot with
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
    let rb ← elabE ctxB body (if elseE.isNone then some .void else exp.map refine)
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
    -- (a local from outside the branch that it gives, at its own type there,
    -- which refines to its type in the branch: the most general)
    let own (v : SExpr) (t : Ty) : Ty := match v with
      | .ident _ n => if n == D then refine t else ((ctx.lookup n).map (·.ty)).getD (refine t)
      | _ => refine t
    let branchTy : Ty := match Refine.valueOf body, rb.ty with
      | .tuple _ vs, .tup ts => if vs.length == ts.length then .tup ((vs.zip ts).map fun (v, t) => own v t) else refine rb.ty
      | v, t => own v t
    let τ' : Ty := if elseE.isNone then .void else if retOfBranch then branchTy else exp.getD re.ty
    if let some (n, v, _) := opened.find? fun (n, _, _) => τ'.params.contains n then
      eerr p s!"cannot cast {withArticle rx.ty.show} to {T} here: the cast opens {T}'s type argument {v} for the code after it, outside which its value, {withArticle τ'.show}, would name what is unknown (#250)"
    let ret := refine τ'
    discard <| coerce p rb ret
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
      pos := p, bound := D, target := T, tag, continuationScope := ctx.refineScope,
      name := liftName,
      params := ((D, dTy) :: sig).map (fun (n, t) => { name := n, ty := t.toSTy }) ++
        extra.map fun (n, _) => { name := s!"$type{n}", ty := .name n },
      tparams := tps.map fun (n, c) => { pos := p, name := n, constraint := if c then "comparable" else "type" },
      specs, ret := ret.toSTy, branchTy := if retOfBranch then some τ'.toSTy else none, subst := σ, opened := opened.map fun (n, v, _) => (n, v), waits := thenWaits, sourceSuspends,
      exits := Refine.Exits.substTypes ((escRet.map (·.2)).getD {}) σ,
      storage := storage.map fun (n, s) => (n, { frame := s.frame, name := s.name, args := s.args.map Ty.toSTy }),
      inRepeat := ctx.inRepeat, sourceContext := sourceContextOf ctx, liftTag := some ctx.liftTag,
      inlineScopes := ctx.inlineScopes,
      -- (made: a branch the elaborator made, for a cast with clauses
      -- after it, #286, which the source does not have as such)
      -- (and a tagged one, which the source's places do not find, #53)
      body := if ctx.selfClass.isSome || made || D.startsWith "$" || !tag.isEmpty || !ctx.choiceCoercions.isEmpty then some (pruneConstructHints ctxB liftName
        (pruneConstructHints { ctxB with frameName := ctx.frameName } liftName body)) else none }
    modify fun st => if st.castNeeds.any (·.key == key) then st else { st with castNeeds := st.castNeeds ++ [lift] }
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
    -- (then: the object in a slot, and one dispatch per set of pins)
    let (pre, y) ← match rx.e with
      | .local y => pure ([], y)
      | e => do
        let y ← fresh rx.ty
        pure ([Expr.assign y e], y)
    let re ← elseOf
    -- (the branch's own type, when the first elaboration took it; at
    -- another expected type, refused as it was there)
    let τ' : Ty ← if elseE.isNone then pure .void else match exp, l.branchTy with
      | some t, some _ =>
        let ret ← resolveTy env p l.ret
        if ret != t.subst μT then eerr p s!"expected {t.show}, found {ret.show} (the branch of the cast to {shown})"
        pure t
      | some t, none => pure t
      | none, some t => resolveTy env p t
      | none, none => pure re.ty
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
        if sp.name.startsWith "$type" then .app p (.ident p "$witness") [.ident p (sp.name.drop 5).toString] false
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
    be a clause of its own first (`liftCastClause`). `none` without a cast
    to a class. -/
def withCastClauses (ctx : Ctx) (cs : List SExpr) (after : SExpr) (isGen : SExpr → Bool) (asWritten : EM R)
    (rebuild : List SExpr → SExpr → EM R) (later : Bool := false)
    (alone : Nat → String → EM (Option R) := fun _ _ => pure none) : EM (Option R) := do
  -- (`D := T[X]` may be an index, `A[i]`: the one the refusal is at)
  let castAt : List (Nat × Pos) := cs.zipIdx.filterMap fun
    | (.decl _ _ none false (.app q (.ident _ _) [_] true), i) => if later && i == 0 then none else some (i, q)
    | (.app q (.ident _ T) [_] true, i) =>
      if (later && i == 0) || !ctx.types.classes.contains T then none else some (i, q)
    | _ => none
  let inner : List (Nat × Pos) := cs.zipIdx.flatMap fun (c, i) =>
    (Refine.castsIn ctx.types.classes.contains c).map (i, ·)
  if castAt.isEmpty && inner.isEmpty then return none
  let st0 ← get
  match ← tryCatch (Except.ok <$> asWritten) (fun err => pure (Except.error err)) with
  | .ok r => return some r
  | .error err =>
    let some refusal := Refine.castRefusal? err | throw err
    if let some (k, _) := inner.find? (·.2 == refusal.pos) then
      set st0
      let lifted := liftCastClause ctx (Choice.boundIn (cs.take k)) refusal.pos cs[k]!
      return some (← rebuild (cs.take k ++ lifted ++ cs.drop (k + 1)) after)
    let some (k, _) := castAt.find? (·.2 == refusal.pos) | throw err
    let some cast := Refine.castClause? cs[k]! | throw err
    set st0
    if let some r ← alone k err then return some r
    match Refine.castRestClauses (cs.take k) cast refusal.opens (cs.drop (k + 1)) after isGen ctx.types.classes.contains
        (fun n => (ctx.lookup n).any (!·.mutable)) with
    | .ok (cs', after') => return some (← rebuild cs' after')
    | .error why => throw s!"{err} ({why})"

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
             arms := #[(ctx, alts)], itemCode := vd, next := start + alts.length }

/-- (#283) A return frame of a lazily taken recursive group: the code after a
    call of the group in an alternative, `$then(call, hole, code)`, which
    runs on each of the call's values, bound to `hole`. `lives` are the names
    of the alternative's context (`ctx`) the code uses: their values when
    the call is made are kept in the frame, pushed on the continuation of
    the call's items. `pre`: the clauses that run before the call, with its
    arguments (what the alternative reads before the call that may not read
    the same after it, bound to names), elaborated once; `ctx` has their
    names. -/
structure LoopFrame where
  hole : String
  lives : List Local
  code : SExpr
  ctx : Ctx
  pre : Option Expr := none
  /-- Where the prefix sets a name, which the next alternative would see. -/
  preSet : Option Pos := none

/-- The return frames of a tail's alternatives, in the order of its arms. -/
def loopFramesWith (elabSeq : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (arms : List (Ctx × List SExpr)) : EM (List LoopFrame) := do
  let mut out : List LoopFrame := []
  for (ca, as) in arms do
    for a in as do
      if let .app _ (.ident _ "$then") (_ :: .ident _ h :: k :: rest) false := a then
        let (pre, c) ← match rest with
          | [.block _ ss] => do
            let (r, c) ← elabSeq { ca with canFail := true, inTaking := true } ss none
            pure (some r.e, { c with canFail := ca.canFail, inTaking := ca.inTaking })
          | _ => pure (none, ca)
        let own := h :: Choice.localsOf k
        let preSet := rest.findSome? fun e => if Choice.anyE (fun | .set .. => true | _ => false) e then some e.pos else none
        out := out ++ [{ hole := h, code := k, ctx := c, pre, preSet,
                         lives := (Choice.namesUsed k).eraseDups.filterMap fun n => if own.contains n then none else c.lookup n }]
  return out

/-- A return frame's lives' values (`void` for none, as `tuple()` is). -/
def frameLivesTy (ts : List Ty) : Ty := if ts.isEmpty then .void else .tup ts

/-- A frame on a continuation: one option per return frame, the one of the
    call that pushed it holding its lives' values. -/
def frameTy (lives : List (List Ty)) : Ty := .tup (lives.map fun ts => .opt (frameLivesTy ts))

/-- The continuation of a lazily taken recursive group (#283): its frames,
    innermost first, a list of `$lazycell`s. -/
def frameContTy (lives : List (List Ty)) : Ty := .opt (.struct "$lazycell" [frameTy lives])

/-- The lives' types of each return frame, from its continuation's type. -/
def frameLivesOf : Ty → Option (List (List Ty))
  | .opt (.struct "$lazycell" [.tup fs]) => fs.mapM fun | .opt .void => some [] | .opt (.tup ts) => some ts | _ => none
  | _ => none

/-- The continuation `k` with frame `j` pushed on it, holding `vals`. -/
def framePush (ctx : Ctx) (lives : List (List Ty)) (j : Nat) (vals : List Expr) (k : Expr) : Expr :=
  let fr : Expr := .prim .mkTup (lives.zipIdx.map fun (_, i) =>
    if i == j then .prim .mkSome [if vals.isEmpty then .lit .void else .prim .mkTup vals] else .lit .none)
  .prim .mkSome [.heap (.new (ctx.types.tagOf "$lazycell")) [fr, k]]

/-- The value `leaf` given to the continuation `k` (#283): each frame's code
    in turn, innermost first, on the value the one before gave, with the
    frame's lives in slots of their own (the item's names stay as they are),
    until no frame is left. It runs where the value does, in the consumer's
    failure context, so what the frames do is undone with the value. -/
def frameApplyWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (p : Pos)
    (frames : List LoopFrame) (rty : Ty) (k leaf : Expr) : EM Expr := do
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
  let mut arms : List (Nat × Nat × Expr) := []
  for (f, j) in frames.zipIdx do
    let t ← fresh (frameLivesTy (f.lives.map (·.ty)))
    let ls ← f.lives.mapM fun l => do return { l with slot := ← fresh l.ty }
    let h ← fresh rty
    let hole : Local := { name := f.hole, slot := h, ty := rty, mutable := false }
    let c : Ctx := { f.ctx with canFail := true, inTaking := true, locals := hole :: ls.reverse ++ f.ctx.locals }
    let r ← elabE c f.code (some rty)
    let e ← coerce f.code.pos r rty
    let unpack := ls.zipIdx.foldr (fun (l, i) acc => Expr.seq (.assign l.slot (.prim (.tupGet i) [.local t])) acc) vd
    arms := arms ++ [(j, t, .seq unpack (.seq (.assign h (.local v)) (.seq (.assign v e) vd)))]
  let dispatch : Expr := arms.foldr (fun (j, t, body) acc =>
    .ite (.assign t (.prim .query [.prim (.tupGet j) [.local fr]])) body acc) vd
  let step : Expr := .ite (.assign cell (.prim .query [.local kk]))
    (.seq (.assign fr (.heap (.get itemF) [.local cell])) (.seq (.assign kk (.heap (.get nextF) [.local cell])) dispatch))
    Expr.brkV
  return .seq (.assign v leaf) (.seq (.assign kk k) (.seq (.loop step) (.local v)))

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
      for (ca, alts) in code.arms do
        for alt in alts do
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
  -- (#283) the return frames of the alternatives that are calls with code
  -- after them, and the continuation they are pushed on, which every item
  -- keeps, after every member's names
  let frames ← loopFramesWith elabSeq (infos.toList.flatMap fun (_, code, _) => code.arms.toList)
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
  -- (the alternatives, numbered across the members' branches)
  let mut offs : Array Nat := #[]
  let mut total : Nat := 0
  for (_, armCode, _) in infos do
    offs := offs.push total
    total := total + armCode.next
  let mut alts : Array Expr := #[]
  let mut values : Array (Nat × Expr) := #[]
  let mut itemCode : Expr := vd
  let mut argSet : Option Pos := none
  let mut starts : Array Expr := #[]
  let mut fi : Nat := 0
  for ((rc, armCode, _), i) in infos.toList.zipIdx do
    let off := offs.getD i 0
    itemCode := .seq itemCode (.seq rc.e armCode.itemCode)
    let firsts : List Nat := (armCode.arms.toList.foldl (fun (acc, n) (_, as) => (acc ++ [n], n + as.length)) ([], off)).1
    let select := .seq armCode.select (.assign k (p2 .add (.local k) (.lit (.int (off : Nat)))))
    starts := starts.push (.ite (.seq rc.e select) vd (.seq (.assign k (.lit (.int (total : Nat)))) vd))
    for ((ca, as), first) in armCode.arms.toList.zip firsts do
      for (a, j) in as.zipIdx do
        let gi := first + j
        let actx : Ctx := { ca with canFail := true, inTaking := true }
        let next? : Option Nat := if j + 1 < as.length then some (gi + 1) else none
        let cont : Expr := match next? with
          | some n => push (item (.lit (.int (n : Nat))) cur)
          | none => vd
        -- (a call with code after it: its return frame, pushed with it)
        let (a, frame?) := match a, kl? with
          | .app _ (.ident _ "$then") (c :: _) false, some kl => (c, some (fi, kl))
          | a, _ => (a, none)
        if frame?.isSome then fi := fi + 1
        -- (its prefix, if any: before the arguments, in whose context they are)
        let fr? := frame?.bind fun (j, _) => frames[j]?
        let pre? := fr?.bind (·.pre)
        let actx : Ctx := match pre?, fr? with
          | some _, some f => { f.ctx with canFail := true, inTaking := true }
          | _, _ => actx
        let call? : Option (Nat × List SExpr × Pos) := match a with
          | .app q (.ident _ "$rec") args' false => some (i, args', q)
          | .app q (.ident _ "$recTo") (.ident _ h :: args') false => (names.idxOf? h).map (·, args', q)
          | _ => none
        match call? with
        | some (jm, args', q) =>
          let some (h, hpls, _, _) := ms[jm]? | eerr q "internal: a call in a group (#283)"
          if argSet.isNone then
            argSet := args'.findSome? fun a' =>
              if Choice.anyE (fun | .set .. => true | _ => false) a' then some a'.pos else none
          if argSet.isNone then argSet := fr?.bind (·.preSet)
          let ts ← hpls.mapM fun l => fresh l.ty
          let assigns ← elabLoopArgsWith elabE actx q h args' hpls ts ((instances.lookup h).getD [])
          let assigns := match pre? with | some e => Expr.seq e assigns | none => assigns
          itemCode := .seq itemCode assigns
          let kE := frame?.map fun (j, kl) =>
            framePush ctx lives j (((frames[j]?).map (·.lives)).getD [] |>.map (Expr.local ·.slot)) (.local kl.slot)
          alts := alts.push (.ite assigns (.seq cont (push (startOf jm ts kE))) cont)
        | none =>
          let r ← elabE actx a (some rty)
          values := values.push (gi, ← coerce a.pos r rty)
          let nextK : Int := match next? with | some n => (n : Int) | none => -1
          alts := alts.push (.seq (.assign nx (.lit (.int nextK))) (.seq (.assign has (.lit (.logic true))) vd))
  let dispatch : Expr := (alts.toList.zipIdx).foldr (fun (a, i) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) a acc) vd
  let unpack : Expr := (all.zipIdx).foldr (fun (l, j) acc =>
    .seq (.assign l.slot (.prim (.tupGet (j + 1)) [.local it])) acc) vd
  let init : Expr := .seq (.assign w (.lit .none)) (.seq (.assign sp (.lit (.int 0)))
    (push (item (.lit (.int (-1))) (args.map (Expr.local ·.slot) ++ cur.drop pls0.length))))
  let init : Expr := match kl? with
    | some kl => .seq (.assign kl.slot (.lit .none)) init
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
  let value : Expr := values.toList.foldr (fun (i, e) acc =>
    .ite (p2 .eq (.local k) (.lit (.int (i : Nat)))) e acc) (.prim .fail [])
  -- (#283) given to the frames of the item's continuation)
  let value ← match kl? with
    | some kl => frameApplyWith elabE ctx p frames rty (.local kl.slot) value
    | none => pure value
  let after : Expr := .ite (p2 .ge (.local nx) (.lit (.int 0))) (push (item (.local nx) cur)) vd
  return { init, step, sp, has, value, after, vty := rty, itemCode, argSet, instances,
           frames := frames.map (fun f => (f.hole, f.lives.map (·.name), f.code)), kTy := kl?.map (·.ty) }

/-- (#283) A body for the elaboration that chooses overloads: each
    `$inlineOv(F, id, call, …)` its call as written, `$ovPick(id, F, call)`. -/
partial def ovForTypes : SExpr → SExpr :=
  Choice.mapE fun
    | .app p (.ident _ "$inlineOv") (.ident q f :: .int _ id :: call :: _) false =>
      some (.app p (.ident p "$ovPick") [.int p id, .ident q f, ovForTypes call] false)
    | _ => none

/-- (#283) The body with each `$inlineOv` its chosen overload's inlined
    call, `picks` the overload (`F$ovK`) each id's call took. -/
partial def ovChosen (picks : List (Nat × String)) : SExpr → SExpr :=
  Choice.mapE fun
    | .app p (.ident _ "$inlineOv") (.ident q f :: .int _ id :: _ :: cands) false =>
      let k? : Option Nat := (picks.lookup id.toNat).bind fun o => ((o.splitOn "$ov").getLast?).bind (·.toNat?)
      match k?.bind (cands[·]?) with
      | some c => some (ovChosen picks c)
      | none => some (.app p (.ident p "$ovUnresolved") [.ident q f] false)
    | _ => none

/-- Check a construction's value choices at the field's expected type.
    Keeping the original inline/lazy templates visits nested constructions
    under their real parameter aliases, rather than replacing them by calls. -/
def constructFieldsForTypes : SExpr → SExpr
  | .decl p f t v x =>
    .decl p f t v (if Choice.hasLiftable x then
      .app x.pos (.ident x.pos "$constructValuesType") [x] false else x)
  | e => e

end OpenVerse.Front
