/- Elaboration application; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse
set_option maxHeartbeats 800000 in
partial def elabAppBaseWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (withDeferMark : Ctx → Expr → EM Expr)
    (elabSpawn : Ctx → Pos → SExpr → EM R)
    (resolveOverload : Ctx → Pos → String → List String → (String → Option Sig) → (String → EM R) → List SExpr → EM R)
    (elabArgs : Ctx → Pos → List SExpr → List Ty → EM (List Expr))
    (elabInts : Ctx → Pos → List SExpr → EM (List Expr))
    (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (elabCast : Ctx → Pos → String → List SExpr → Bool → EM R)
    (elabGenericCall : Ctx → Pos → Sig → List SExpr → Option Ty → EM R)
    (elabMethod : Ctx → Pos → R → String → List SExpr → Bool → EM R)
    (elabIndexLike : Ctx → Pos → R → List SExpr → Bool → EM R)
    (elabSpawnDispatch : Ctx → Pos → String → String → String → List SExpr → Option Ty → EM R)
    (elabDefaultDispatch : Ctx → Pos → String → List SExpr → Bool → Option Ty → EM R)
    (elabMember : Ctx → Pos → R → String → optParam (Option Ty) none → EM R)
    (ctx : Ctx) (p : Pos) (f : SExpr) (args : List SExpr) (bracket : Bool)
    (exp : Option Ty) : EM R := do
  let needBracket (name : String) : EM Unit := do
    if !bracket then eerr p s!"{name} can fail: call it with {name}[…]"
  let indexLike (source : SExpr) (value : R) : EM R := do
    if !ctx.typeOnly && ctx.isTypeValue source then
      let view ← match ctx.callableView source.pos value.ty with
        | .ok view => pure view
        | .error message => throw message
      if view.isSome then eerr source.pos "dummy type value cannot be an executable function"
    elabIndexLike ctx p value args bracket
  match f with
  | .ident _ name =>
    match ctx.lookup name with
    | some l => indexLike f ⟨.local l.slot, l.ty⟩
    | none =>
    -- in a method, a method of `Self`, or a field of `Self` indexed
    let selfMember? : Bool := match ctx.selfClass with
      | some c => ctx.hasMethod c name ||
          ((ctx.types.methodOverloads.lookup name).map (·.any (ctx.hasMethod c ·))).getD false ||
          ((ctx.types.fields c).any (·.1 == name) && !builtins.contains name && !softBuiltins.contains name)
      | none => false
    if selfMember? then elabApp ctx p (.member p (.ident p "Self") name) args bracket exp else
    -- `T[X]`, `T(X)`: a cast to class or interface `T`
    if ctx.types.classes.contains name && (ctx.sig? name).isNone then elabCast ctx p name args bracket else
    if let some (base, conds) := ctx.types.refines.lookup name then
      -- `age[X]` (#136): `X`, if it meets the conditions; failing otherwise
      if !bracket then eerr p s!"a cast to {name} can fail: write {name}[X]"
      let [a] := args | eerr p s!"a cast to {name} takes one value"
      let r ← elabE ctx a (some base)
      let r := widenR ctx.types r
      if r.ty != base then eerr p s!"a cast to {name} takes {withArticle base.show}, found {r.ty.show}"
      let tv ← fresh base
      let isF := base == .float
      let test (c : String × Value) : Expr :=
        let op : Prim := match c.1, isF with
          | "<", false => .lt | "<=", false => .le | ">", false => .gt | _, false => .ge
          | "<", true => .flt | "<=", true => .fle | ">", true => .fgt | _, true => .fge
        p2 op (.local tv) (.lit c.2)
      let checks := conds.foldr (fun c acc => Expr.seq (test c) acc) (.local tv)
      return ⟨.seq (.assign tv r.e) checks, .refine name⟩
    else
    if let some ovs := ctx.types.overloads.lookup name then
      resolveOverload ctx p name ovs ctx.sig? (fun o => do
        -- (#283) the overload an `$inlineOv`'s call as written takes
        if let some (id, f) := ctx.ovPick then
          if f == name then modify fun st => { st with ovPicks := (id, o) :: st.ovPicks }
        elabApp { ctx with ovPick := none } p (.ident p o) args bracket exp) args
    else
    -- (a soft built-in the program defines is the program's)
    let builtinName := if (softBuiltins.contains name || name == "any") && (ctx.sig? name).isSome then "$program" else name
    match builtinName with
    | "Concatenate" =>
      -- (#150) an array of arrays flattened, or several arrays one after
      -- the other (as a tuple of them converts to an array of arrays)
      match args with
      | [] => match exp with
        | some (.arr t) => return ⟨.lit Value.emptyArray, .arr t⟩
        | _ => eerr p "Concatenate() needs an expected array type"
      | [a] =>
        let r ← elabE ctx a (match exp with | some t => some (.arr t) | none => none)
        match r.ty with
        | .arr (.arr t) =>
          -- (through a typed temporary: an empty literal has no type of its own)
          let tv ← fresh r.ty
          return ⟨.seq (.assign tv r.e) (.prim .flatten [.local tv]), .arr t⟩
        | t => eerr p s!"Concatenate takes arrays, or an array of arrays, found {t.show}"
      | a :: rest =>
        let r0 ← elabE ctx a exp
        let .arr t := r0.ty | eerr a.pos s!"Concatenate takes arrays, found {r0.ty.show}"
        let mut acc := r0.e
        for b in rest do
          let rb ← elabE ctx b (some (.arr t))
          acc := p2 .concat acc (← coerce b.pos rb (.arr t))
        return ⟨acc, .arr t⟩
    | "any" =>
      -- `any(X)`: X as an `any` (#138), evaluated
      let [a] := args | eerr p "any(…) takes one value"
      let r ← elabE ctx a none
      return ⟨← coerce a.pos r .any, .any⟩
    | "Print" =>
      let es ← elabArgs ctx p args [Ty.string]
      return ⟨.print es.head!, .void⟩
    | "ConcatenateMaps" =>
      -- the entries of every map, a later map's value winning for a key (Book
      -- of Verse ch. 9): the first copied, then each other's pairs put in turn
      let some a0 := args.head? | eerr p "ConcatenateMaps takes at least one map"
      -- the maps' type: the expected one, else the first argument's that has
      -- one alone (an empty map{} has none)
      let mapExp : Option Ty ← match exp with
        | some t@(.map ..) => pure (some t)
        | _ =>
          let st ← get
          let mut found : Option Ty := none
          for a in args do
            if found.isNone then
              found ← tryCatch (do let r ← elabE ctx a none; pure (match r.ty with | t@(.map ..) => some t | _ => none))
                (fun _ => pure none)
          set st
          pure found
      let mut rs : Array R := #[]
      let mut jt? : Option Ty := none
      for a in args do
        let r ← elabE ctx a mapExp
        let .map _ _ := r.ty | eerr a.pos s!"ConcatenateMaps takes maps, not {r.ty.show}"
        match jt? with
        | none => jt? := some r.ty
        | some j =>
          let j' ← tryCatch (join a.pos j r.ty mapExp) (fun _ =>
            eerr a.pos s!"ConcatenateMaps takes maps of one type, not {j.show} and {r.ty.show}")
          jt? := some j'
        rs := rs.push r
      let some jt := jt? | eerr p "ConcatenateMaps takes at least one map"
      let .map kt vt := jt | eerr p s!"ConcatenateMaps takes maps, not {jt.show}"
      let tm ← fresh jt
      let some r0 := rs[0]? | eerr p "ConcatenateMaps takes at least one map"
      let mut code : Expr := .assign tm (← coerce a0.pos r0 jt)
      for (r, a) in rs.toList.tail.zip args.tail do
        let ts ← fresh jt
        let tpair ← fresh (.tup [kt, vt])
        let tk ← fresh kt
        let tv ← fresh vt
        let ti ← fresh .int
        let tidx ← fresh .int
        let put := Expr.seq (.assign tk (.prim (.tupGet 0) [.local tpair]))
          (.seq (.assign tv (.prim (.tupGet 1) [.local tpair])) (mapPut tm tk tv ti tidx))
        code := .seq code (.seq (.assign ts (← coerce a.pos r jt)) (.forE tpair (.local ts) (.lit (.logic true)) put))
      return ⟨.seq code (.local tm), jt⟩
    | "ToString" =>
      match args with
      | [a] => return ⟨← toStringOf p (← elabE ctx a none), Ty.string⟩
      | _ => eerr p "ToString takes one argument"
    | "Abs" =>
      -- (of a float, #127; each argument elaborated once)
      match args with
      | [a] =>
        let r ← elabE ctx a none
        if r.ty == .float then return ⟨.prim .fabs [r.e], .float⟩
        return ⟨.prim .abs [← coerce a.pos r .int], .int⟩
      | _ => eerr p "Abs takes one argument"
    | "Sqrt" | "Exp" | "Ln" | "Log" | "Pow" | "Sin" | "Cos" | "Tan" | "ArcSin" | "ArcCos" | "ArcTan"
    | "IsFinite" | "Sinh" | "Cosh" | "Tanh" | "ArSinh" | "ArCosh" | "ArTanh" | "Lerp" =>
      -- the mathematical functions of floats (#132); only IsFinite fails
      if name == "IsFinite" then needBracket name
      else if bracket then eerr p s!"{name} cannot fail: call it with {name}(…)"
      if ["Sinh", "Cosh", "Tanh", "ArSinh", "ArCosh", "ArTanh", "Lerp"].contains name then
        noteFx p ["reads"] (some name)
      let fl (a : SExpr) : EM Expr := do
        let r := widenR ctx.types (← elabE ctx a (some .float))
        if r.ty != .float then eerr a.pos s!"{name} takes floats, found {r.ty.show}"
        return r.e
      let unary : String → Option Prim
        | "Sqrt" => some .fsqrt | "Exp" => some .fexp | "Ln" => some .fln | "Sin" => some .fsin
        | "Cos" => some .fcos | "Tan" => some .ftan | "ArcSin" => some .fasin | "ArcCos" => some .facos
        | "ArcTan" => some .fatan | "IsFinite" => some .fisFinite
        | "Sinh" => some .fsinh | "Cosh" => some .fcosh | "Tanh" => some .ftanh
        | "ArSinh" => some .fasinh | "ArCosh" => some .facosh | "ArTanh" => some .fatanh
        | _ => none
      match name, args with
      | "Lerp", [a, b, parameter] =>
        let ta ← fresh .float
        let ea ← fl a
        let tb ← fresh .float
        let eb ← fl b
        let tp ← fresh .float
        let ep ← fl parameter
        let one := Expr.lit (.float 0x3FF0000000000000)
        let blend := p2 .fadd (p2 .fmul (.local ta) (p2 .fsub one (.local tp)))
          (p2 .fmul (.local tb) (.local tp))
        return ⟨.seq (.assign ta ea) (.seq (.assign tb eb) (.seq (.assign tp ep) blend)), .float⟩
      | "Pow", [a, b] => return ⟨p2 .fpow (← fl a) (← fl b), .float⟩
      | "ArcTan", [y, x] => return ⟨p2 .fatan2 (← fl y) (← fl x), .float⟩
      | "Log", [b, x] =>
        -- (`Log(Base, X)` is `Ln(X) / Ln(Base)`, the base evaluated first)
        let tb ← fresh .float
        let eb ← fl b
        let ex ← fl x
        return ⟨.seq (.assign tb eb) (p2 .fdiv (.prim .fln [ex]) (.prim .fln [.local tb])), .float⟩
      | n, [a] =>
        match unary n with
        | some op => return ⟨.prim op [← fl a], .float⟩
        | none => eerr p s!"{name} takes {if name == "Lerp" then "three" else "two"} floats"
      | _, _ => eerr p s!"{name} takes {if name == "Lerp" then "three floats" else if name == "Pow" || name == "Log" then "two floats" else if name == "ArcTan" then "one or two floats" else "one float"}"
    | "Round" | "$Round" | "Int" =>
      -- a float to an int (#127): `Round` ties to even, `Int` towards zero;
      -- failing on NaN, an infinity or out of range
      let shown := if name == "$Round" then "Round" else name
      needBracket shown
      match args with
      | [a] =>
        let r := widenR ctx.types (← elabE ctx a (some .float))
        if r.ty != .float then eerr p s!"{shown} takes a float, found {r.ty.show}"
        return ⟨.prim (if shown == "Round" then .fround else .ftrunc) [r.e], .int⟩
      | _ => eerr p s!"{shown} takes one argument"
    | "Floor" | "Ceil" =>
      -- (of a float, #127: failable, so with brackets; of a rational or
      -- an int, with either, as the Book writes both)
      let ofFloat (r : R) : EM R := do
        if !bracket then eerr p s!"{name} of a float can fail: call it with {name}[…]"
        return ⟨.prim (if name == "Floor" then .ffloor else .fceil) [r.e], .int⟩
      match args with
      | [.bin bp "/" a b] =>
        let ra ← elabE ctx a none
        let rb ← elabE ctx b (if ra.ty == .float then some .float else none)
        if ra.ty == .float && rb.ty == .float then return ← ofFloat ⟨p2 .fdiv ra.e rb.e, .float⟩
        if ra.ty == .float || rb.ty == .float then
          eerr bp s!"no operator '/' for {ra.ty.show} and {rb.ty.show} (an int is not a float: write X * 1.0)"
        if ra.ty == .rational || rb.ty == .rational then
          return ⟨← roundRational (name == "Ceil") (← rationalBinary bp .quotient ra rb), .int⟩
        let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
        return ⟨.prim (if name == "Floor" then .floorDiv else .ceilDiv) es, .int⟩
      | [e] =>
        -- (of a rational, #116: its denominator is positive, so this never
        -- fails; of an int, the int)
        let r := widenR ctx.types (← elabE ctx e none)
        match r.ty with
        | .int => return r
        | .float => ofFloat r
        | .rational =>
          return ⟨← roundRational (name == "Ceil") r.e, .int⟩
        | t => eerr p s!"{name} takes a rational or an int, found {t.show}"
      | _ => eerr p s!"{name} takes one argument"
    | "Quotient" => needBracket name; return ⟨.prim .quotient (← elabInts ctx p args), .int⟩
    | "Mod" => needBracket name; return ⟨.prim .modulo (← elabInts ctx p args), .int⟩
    | "Min" | "Max" =>
      -- (of floats, #127: NaN when either is)
      -- (each argument elaborated once)
      let [a, b] := args | eerr p s!"{name} takes two arguments"
      let ra ← elabE ctx a none
      let rb ← elabE ctx b (if ra.ty == .float || ra.ty == .int then some ra.ty else none)
      if ra.ty == .float then
        if rb.ty != .float then eerr p s!"{name} takes two floats or two ints, found float and {rb.ty.show}"
        return ⟨p2 (if name == "Min" then .fmin else .fmax) ra.e rb.e, .float⟩
      let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
      let ta ← fresh .int
      let tb ← fresh .int
      let op := if name == "Min" then Prim.le else Prim.ge
      return ⟨.seq (.assign ta es[0]!) (.seq (.assign tb es[1]!)
        (.ite (p2 op (.local ta) (.local tb)) (.local ta) (.local tb))), .int⟩
    | "Err" =>
      modify fun st => if st.errAt.isNone then { st with errAt := some p } else st
      return ⟨.prim .userErr [], .never⟩
    | "$Show" =>
      -- the entry of `openverse run FILE do EXPR`: print the value when it
      -- has a ToString, else just evaluate it
      match args with
      | [a] =>
        let r ← elabE ctx a none
        match r.ty with
        | .int | .char | .float | .arr .char => return ⟨.print (← toStringOf p r), .void⟩
        | _ => return ⟨.seq r.e (.lit .void), .void⟩
      | _ => eerr p "internal: $Show"
    | _ =>
      -- `Sleep` (#156): the concurrency helpers' unless the program has its own
      let name := if name == "Sleep" && (ctx.sig? "Sleep").isNone then "$Sleep" else name
      if name == "$Sleep" && (ctx.sig? name).isNone then
        eerr p "Sleep suspends: it can only be called in a <suspends> function (#156)"
      match ctx.sig? name with
      | some s =>
        -- a call has its callee's effects
        noteFx p s.fx (some (if s.isConst then s!"uses the constant {name}" else s!"calls {name}"))
        if s.isConst then
          indexLike f ⟨.call s.idx [], s.ret⟩
        else
          let args := packCallArgs p s args
          if s.decides && !bracket then eerr p s!"{name} is <decides>: call it with {name}[…]"
          -- the call syntax marks failure (Book of Verse §8.1)
          if !s.decides && bracket then eerr p s!"{name} cannot fail: call it with {name}(…)"
          if s.suspends then
            let shown := if name == "$EvAwait" then "Await"
              else if name.startsWith "$" then (name.drop 1).toString else name
            if !ctx.suspends then eerr p s!"{shown} suspends: it can only be called in a <suspends> function (#156)"
            if ctx.inDefer then eerr p s!"{shown} suspends, and a defer cannot suspend (#156)"
            if ctx.canFail then eerr p s!"{shown} suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
          if !s.tparams.isEmpty then
            let r ← elabGenericCall ctx p s args exp
            if s.suspends then return ⟨← withDeferMark ctx r.e, r.ty⟩ else return r
          let isNamed : SExpr → Bool
            | .decl _ n _ _ _ => n.startsWith "?"
            | _ => false
          -- (a suspension point records the defers active there, #156)
          let mark (e : Expr) : EM Expr := if s.suspends then withDeferMark ctx e else pure e
          if s.named.isEmpty && !args.any isNamed then
            if args.length == 1 && s.params.length > 1 then
              for k in List.range s.params.length do ctx.checkArgumentRole s args[0]! k
            else
              for (argument, index) in args.zipIdx do
                ctx.checkArgumentRole s argument (if s.params.length == 1 then 0 else index)
            -- a tuple for several parameters is expanded into them (Book of
            -- Verse ch. 3: `Describe(MyTuple)` is `Describe(1, "two")`)
            if let [a] := args then
              if s.params.length > 1 then
                let r ← elabE ctx a (some (.tup s.params))
                if let .tup ts := r.ty then
                  if ts.length == s.params.length then
                    let tt ← fresh r.ty
                    -- (an element that never gives a value left before the
                    -- call: `Err()` in its place, of every type, #290)
                    let parts ← ((s.params.zip ts).zip (List.range ts.length)).mapM fun ((pt, et), i) =>
                      if et == .never then pure (.prim .userErr [])
                      else coerce a.pos ⟨.prim (.tupGet i) [.local tt], et⟩ pt
                    return ⟨← mark (.seq (.assign tt r.e) (.call s.idx parts)), s.ret⟩
                let (shown, off) := match name.splitOn "." with
                  | [_, m] => if s.pnames.head? == some "Self" then (m, 1) else (name, 0)
                  | _ => (name, 0)
                eerr p s!"{shown} takes {s.params.length - off} argument(s), found 1 (of type {r.ty.show})"
            -- several arguments for one array parameter make the array
            -- (`Sum(1, 2, 3, 4)`, as a tuple converts to an array)
            if let [.arr et] := s.params then
              if args.length > 1 then
                let es ← elabArgs ctx p args (args.map fun _ => et)
                return ⟨← mark (.call s.idx [.prim .mkArr es]), s.ret⟩
            let es ← elabArgs ctx p args s.params
            return ⟨← mark (.call s.idx es), s.ret⟩
          -- named arguments: evaluate positional arguments left to right, then named ones as
          -- written, then the defaults of those omitted (Book of Verse §2.5), into temporaries
          let npos := s.params.length - s.named.length
          let pos := args.filter (!isNamed ·)
          let named := args.filterMap fun a => match a with
            | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
            | _ => none
          if pos.length != npos then
            -- a method's receiver is its first positional argument
            let (shown, off) := match name.splitOn "." with
              | [_, m] => (m, 1)
              | _ => (name, 0)
            eerr p s!"{shown} takes {npos - off} positional argument(s), found {pos.length - off}"
          for ((ap, n, _), i) in named.zip (List.range named.length) do
            if (s.named.find? (·.1 == n)).isNone then eerr ap s!"{name} has no parameter ?{n}"
            if (named.take i).any (·.2.1 == n) then eerr ap s!"?{n} is given twice"
          let ptys := s.params.toArray
          let mut steps : Array Expr := #[]
          let mut slots : Array (Option Nat) := Array.replicate s.params.length none
          for (a, k) in pos.zip (List.range npos) do
            ctx.checkArgumentRole s a k
            let t := ptys[k]!
            let ta ← fresh t
            steps := steps.push (.assign ta (← coerce a.pos (← elabE ctx a (some t)) t))
            slots := slots.set! k (some ta)
          for (ap, n, rhs) in named do
            let k := npos + (s.named.findIdx? (·.1 == n)).get!
            ctx.checkArgumentRole s rhs k
            let t := ptys[k]!
            let ta ← fresh t
            steps := steps.push (.assign ta (← coerce ap (← elabE ctx rhs (some t)) t))
            slots := slots.set! k (some ta)
          for ((n, dflt), j) in s.named.zip (List.range s.named.length) do
            let k := npos + j
            if slots[k]!.isNone then
              let some d := dflt | eerr p s!"{name} needs the argument ?{n}, which has no default"
              let t := ptys[k]!
              let ta ← fresh t
              -- (the default sees the parameters before it, in their temporaries)
              let earlier : List Local := ((s.pnames.zip (List.range k)).filterMap fun (pn, j) =>
                (slots[j]!).map fun sl => ({ name := pn, slot := sl, ty := ptys[j]!, mutable := false, typeValue := s.typeValues.contains j } : Local)).reverse
              -- (a method's: its receiver's fields too, through `Self`; a
              -- copy's in its interface's scope, as its body, #53)
              let selfC : Option String :=
                if s.pnames.head? == some "Self" then s.scope.orElse fun _ => (s.name.splitOn ".").head? else none
              -- (its own context: no return or break into the caller, failure
              -- only for a <decides> callee, and not its own default again)
              let key := (s.name, s!"?{n}")
              if ctx.defaults.contains key then
                eerr p s!"the default of ?{n} of {name} uses itself (a call of {name} that omits ?{n})"
              let dctx := { ctx with locals := earlier, selfClass := selfC,
                                     selfMethod := if selfC.isSome then (s.name.splitOn ".").getLast? else none,
                                     inParamDefault := true,
                                     inLoop := false, canFail := ctx.canFail && s.decides,
                                     suspends := ctx.suspends && s.suspends,
                                     defaults := key :: ctx.defaults }
              dctx.checkArgumentRole s d k
              let rd ← fxAt p (do coerce p (← elabE dctx d (some t)) t)
              if !s.decides && rd.mayFail ctx.sigProg then
                eerr p s!"the default of ?{n} of {name} can fail, but {name} is not <decides>"
              steps := steps.push (.assign ta rd)
              slots := slots.set! k (some ta)
          let call := Expr.call s.idx (slots.toList.map fun o => Expr.local o.get!)
          let e := steps.toList.foldr Expr.seq call
          return ⟨← mark e, s.ret⟩
      | none =>
        if (ctx.sig? s!"{name}$init").isSome || (ctx.types.overloads.lookup s!"{name}$init").isSome then
          eerr p s!"{name} constructs an abstract class: it can only be delegated to, as {name}<constructor>(…) in a constructor of a class below it"
        eerr p s!"unknown function '{name}'"
  | .member mp (.ident _ "(super:)") m =>
    -- `(super:)M(…)`: the implementation the current method's class inherits
    let some c := ctx.selfClass | eerr p "(super:) can only be used in a method"
    if let some ms := (if (ctx.methodDecl? c m).isNone then ctx.types.methodOverloads.lookup m else none) then
      -- (the overloads above `c`)
      let above := (ctx.types.supers c).drop 1
      let declAbove (o : String) : Option String := above.find? fun e => (ctx.sig? s!"{e}.{o}").isSome
      let sigOf (o : String) : Option Sig := (declAbove o).bind fun owner =>
        (ctx.sig? s!"{owner}.{o}").map fun sg => { sg with params := sg.params.drop 1 }
      let vis := ms.filter fun o => (declAbove o).isSome
      if !vis.isEmpty then
        return ← resolveOverload ctx p m vis sigOf
          (fun o => elabApp ctx p (.member mp (.ident mp "(super:)") o) args bracket exp) args
    let impl ← superImpl ctx p c m
    elabApp ctx p (.ident mp impl) (.ident mp "Self" :: args) bracket exp
  | .member mp obj m0 =>
    if !ctx.typeOnly && ctx.isTypeValue obj then
      eerr mp "dummy type value cannot be an executable method receiver"
    let spawning := m0.startsWith "$spawnMethod:"
    let m0 := if spawning then (m0.drop 13).toString else m0
    -- `T.Await()` of a task (#156): the helper `$Await(T)`
    -- `T.Cancel()` of a task (#156): the mark `$cancelMark(T)`, which the
    -- lowering turns into the cancellation of the task's root
    if m0 == "Cancel" && args.isEmpty then
      let rt ← elabE ctx obj none
      if let .struct n [_] := rt.ty then
        if n == ctx.types.concurrencyName "task" then
          if !ctx.suspends then eerr p "Cancel suspends: it can only be called in a <suspends> function (#156)"
          if ctx.inDefer then eerr p "Cancel suspends, and a defer cannot suspend (#156)"
          if ctx.canFail then eerr p "Cancel suspends, and a failure context (a condition, a filter, or a <decides> call's arguments) cannot (#156)"
          let some mark := ctx.sig? "$cancelMark" | eerr p "internal error: no Cancel helper"
          let t ← fresh rt.ty
          return ⟨.seq (.assign t rt.e) (.call mark.idx [.local t]), .void⟩
    -- `E.Signal()` of an `event()` (#156): with the value `void`
    if m0 == "Signal" && args.isEmpty then
      match (← elabE ctx obj none).ty with
      | .struct n ts =>
        if ((n == ctx.types.concurrencyName "event" || n == ctx.types.concurrencyName "sticky_event") &&
            ts == [.void]) || (n == "$subev0" && ts.isEmpty) then
          return ← elabApp ctx p (.member mp obj "Signal") [.tuple p []] bracket exp
        else pure ()
      | _ => pure ()
    if m0 == "Await" && args.isEmpty then
      match (← elabE ctx obj none).ty with
      | .struct n ts =>
        if n == ctx.types.concurrencyName "task" && ts.length == 1 then
          return ← elabApp ctx p (.ident mp "$Await") [obj] false exp
        else if ((n == ctx.types.concurrencyName "event" || n == ctx.types.concurrencyName "subscribable_event") &&
            ts.length == 1) || (n == "$subev0" && ts.isEmpty) then
          return ← elabApp ctx p (.ident mp "$EvAwait") [obj] false exp
        else if n == ctx.types.concurrencyName "sticky_event" && ts.length == 1 then
          return ← elabApp ctx p (.ident mp "$StickyAwait") [obj] false exp
        else pure ()
      | _ => pure ()
    let r0 ← elabBoundReceiverWith elabE ctx p (← elabE ctx obj none) m0
    -- `X.(i:)M(…)`: `X` as an `i`, so `i`'s `M` (a qualified call)
    let (r, m) ← match r0.ty, m0.startsWith "(", (m0.drop 1).toString.splitOn ":)" with
      | .struct c ts, true, [q, mq] =>
        if !(ctx.types.isSub c q) then eerr p s!"{c} is not below {q}"
        -- (converted: a receiver of a type with no instance is unreachable)
        let qt : Ty := .struct q (ctx.types.upArgs c ts q)
        pure (⟨← coerce p r0 qt, qt⟩, mq)
      | _, _, _ => pure (r0, m0)
    match r.ty with
    | .struct c targs =>
      let env := ctx.types
      -- an overloaded method (#106): the overload visible at `c` the call
      -- fits, then that method
      if let some ms := (if env.classes.contains c && (ctx.methodDecl? c m).isNone then
          env.methodOverloads.lookup m else none) then
        let sigOf (o : String) : Option Sig := (ctx.methodDecl? c o).bind fun owner =>
          (ctx.sig? s!"{owner}.{o}").map fun sg => { sg with params := sg.params.drop 1 }
        let vis := ms.filter fun o => (ctx.methodDecl? c o).isSome
        -- (a qualified call stays qualified: `X.(q:)M$ovK(…)`, #125)
        let qualOf (o : String) : String :=
          if m0.startsWith "(" then
            match (m0.drop 1).toString.splitOn ":)" with
            | [q, _] => s!"({q}:){o}"
            | _ => o
          else o
        if !vis.isEmpty then
          return ← resolveOverload ctx p m vis sigOf (fun o => elabApp ctx p (.member mp obj ((if spawning then "$spawnMethod:" else "") ++ qualOf o)) args bracket exp) args
      if let (true, some owner) := (env.classes.contains c, ctx.methodDecl? c m) then
        -- the slots the call covers (#70): every class below `c` must implement
        -- them alike, or the call must say which
        let roots := ctx.rootsOf c m
        let root := roots.headD owner
        for d in env.concreteBelow c do
          for o in roots do
            if ctx.implFor? d o m != ctx.implFor? d root m then
              eerr p s!"{d} implements {m} separately for {root} and {o}: call it as X.({root}:){m}(…) or X.({o}:){m}(…)"
        let ms := (ctx.sig? s!"{owner}.{m}").get!
        let args := packCallArgs p { ms with params := ms.params.drop 1, pnames := ms.pnames.drop 1 } args false
        if spawning && !ms.suspends then
          eerr p "spawn{…} takes a call of a <suspends> function (#156)"
        if ms.decides && !bracket then eerr p s!"{m} is <decides>: call it with {m}[…]"
        if !ms.decides && bracket then eerr p s!"{m} cannot fail: call it with {m}(…)"
        if ms.named.isEmpty && args.length + 1 != ms.params.length then
          eerr p s!"{m} takes {ms.params.length - 1} argument(s), found {args.length}"
        let slot ← fresh r.ty
        let recv := s!"$recv{slot}"
        let ds := env.concreteBelow c
        -- one implementation for every class below the receiver's type, above
        -- that type: a direct call (the receiver evaluated first, as `Self`)
        let clsOf (fname : String) : String := (fname.splitOn ".").head!
        let direct : Option String := match (ds.map (ctx.implFor? · root m)).eraseDups with
          | [some fname] =>
            let e := clsOf fname
            if !env.isSub c e then none
            -- (#351: at an interface referred to through views, only when
            -- the receiver converts to it; otherwise each class's test,
            -- which a class's pins refine by, `i1(t)` as an `i1(char)`)
            else if env.viewed.contains e && !env.viewed.contains c && c != e then
              match env.viewFits (.struct c targs) (.struct e (if env.isSub c e then env.upArgs c targs e else [])) with
              | some (_, false) => none
              | _ => some fname
            else some fname
          | _ => none
        -- the receiver as an instance of class `e`, above or below `c` (#39)
        let argsAt (e : String) : List Ty :=
          if env.isSub c e then env.upArgs c targs e else env.argsBelow c targs e
        if let some fname := direct then
          let e := clsOf fname
          -- (#351: at an interface referred to through views, the receiver
          -- converted to it, in a slot of its type: a reference through a
          -- prefix one is no reference through views without it)
          let (pre, eslot) ← if env.viewed.contains e && !env.viewed.contains c && c != e then do
              let es ← fresh (.struct e (argsAt e))
              pure ([Expr.assign es (← coerce p ⟨.local slot, r.ty⟩ (.struct e (argsAt e)))], es)
            else pure ([], slot)
          let ctx' := { ctx with
            locals := { name := recv, slot := eslot, ty := .struct e (argsAt e), mutable := false, typeValue := ctx.isTypeValue obj } :: ctx.locals }
          let rc ← if spawning then
              elabSpawn ctx' p (.app p (.ident mp fname) (.ident mp recv :: args) bracket)
            else elabApp ctx' p (.ident mp fname) (.ident mp recv :: args) bracket exp
          return ⟨.seq (.assign slot r.e) (pre.foldr Expr.seq rc.e), rc.ty⟩
        -- otherwise dispatch on the class of the receiver's value: the
        -- receiver, then the arguments, once each, then the implementation of
        -- the class whose option is set
        let ownerTps := ((env.sparams.lookup owner).getD []).map (·.1)
        -- the declaration's types at the receiver's type arguments, its own
        -- type parameters renamed apart (they are inferred from the
        -- arguments below, as for a generic call)
        let ownTps := ms.tparams.drop ownerTps.length
        let ownσ : List (String × Ty) := (ownTps.zip (List.range ownTps.length)).map fun ((v, k), i) =>
          (v, Ty.param s!"$own{i}" k)
        let ownNames := (List.range ownTps.length).map fun i => s!"$own{i}"
        let σ := ownerTps.zip (argsAt owner)
        let declTy (t : Ty) : Ty := (t.subst ownσ).subst σ
        let mut σu : List (String × Ty) := []
        -- the arguments, once each: positional ones left to right, then named
        -- ones as written (Book of Verse §2.5), passed to every implementation;
        -- those omitted take the default of the implementation that runs, as
        -- in a call without named arguments
        let isNamed : SExpr → Bool := fun | .decl _ n _ _ _ => n.startsWith "?" | _ => false
        let posArgs := args.filter (!isNamed ·)
        let namedArgs := args.filterMap fun a => match a with
          | .decl ap n _ _ rhs => if n.startsWith "?" then some (ap, (n.drop 1).toString, rhs) else none
          | _ => none
        let npos := ms.params.length - ms.named.length
        if posArgs.length + 1 != npos then
          eerr p s!"{m} takes {npos - 1} positional argument(s), found {posArgs.length}"
        for (ap, n, _) in namedArgs do
          if (ms.named.find? (·.1 == n)).isNone then eerr ap s!"{m} has no parameter ?{n}"
        let mut pre : Array Expr := #[.assign slot r.e]
        let mut locs : List Local := [{ name := recv, slot, ty := r.ty, mutable := false, typeValue := ctx.isTypeValue obj }]
        let mut argIds : Array SExpr := #[]
        -- the method's own type parameters, from the expected result type
        -- (unless void), then from the arguments, as for a generic call: an
        -- argument is checked against its parameter's type once the own type
        -- parameters it mentions are bound, else inferred from; `false`,
        -- `array{}` and `map{}` take their type from context, so they wait
        -- for the others (they are still evaluated in order)
        let showT (t : Ty) : String :=
          (t.subst ((ownNames.zip ownTps).map fun (n, (v, k)) => (n, Ty.param v k))).show
        let own? (σ' : List (String × Ty)) := σ'.filter fun (v, _) => ownNames.contains v
        if let some et := exp then
          if !(et == .void) then
            if let some σ' := (declTy ms.ret).matchArg ctx.types σu et then σu := own? σ'
        -- Infer from all given arguments before checking contextual values,
        -- preserving positional then written named order in the emitted code.
        let given : List (SExpr × Ty × Option String) :=
          (posArgs.zip ((ms.params.drop 1).take (npos - 1))).map (fun (a, t) => (a, t, none)) ++
          namedArgs.map (fun (_, n, rhs) =>
            (rhs, ms.params[npos + (ms.named.findIdx? (·.1 == n)).get!]!, some n))
        let contextual := (← given.mapM (fun (a, _, _) => argNeedsTypeWith elabE ctx a)).toArray
        let mut done : Array (Option (Expr × Ty)) := Array.replicate given.length none
        let mut deferred : Array Bool := contextual
        for pass in [0, 1] do
          for ((a, t0, _), i) in given.zipIdx do
            if (pass == 0) == deferred[i]! then continue
            let t := (declTy t0).subst σu
            if t.params.any ownNames.contains then
              if contextual[i]! then
                eerr a.pos s!"cannot infer the type parameters of {m} from the arguments of this call"
              let r ← elabE ctx a none
              match t.matchArg ctx.types σu r.ty with
              | some σ' =>
                σu := own? σ'
                let t' := t.subst σu
                if t'.params.any ownNames.contains then
                  if pass == 0 then deferred := deferred.set! i true
                  else eerr a.pos s!"cannot infer the type parameters of {m} from this argument"
                else done := done.set! i (some (← coerce a.pos r t', t'))
              | none => eerr a.pos s!"expected {showT t}, found {r.ty.show} (in a call of {m})"
            else
              done := done.set! i (some (← coerce a.pos (← elabE ctx a (some t)) t, t))
        let mut namedSlots : List (String × Nat) := []
        for ((argument, _, name), d) in given.zip done.toList do
          let some (e, t) := d | eerr p s!"cannot infer the type parameters of {m} from the arguments of this call"
          let ta ← fresh t
          pre := pre.push (.assign ta e)
          locs := { name := s!"$arg{ta}", slot := ta, ty := t, mutable := false, typeValue := ctx.isTypeValue argument } :: locs
          match name with
          | none => argIds := argIds.push (.ident mp s!"$arg{ta}")
          | some n => namedSlots := namedSlots ++ [(n, ta)]
        for (n, ta) in namedSlots do
          argIds := argIds.push (.decl mp s!"?{n}" none false (.ident mp s!"$arg{ta}"))
        let msRet := (declTy ms.ret).subst σu
        if msRet.params.any ownNames.contains then
          eerr p s!"cannot infer the type parameters of {m} from the arguments of this call"
        if spawning then
          let isS (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.suspends
          let skip (f : Nat) := ctx.sigs.any fun s => s.idx == f && s.name == "$spawnMark"
          if pre.any (fun e => Suspend.countSusp isS (fun _ => false) false skip e > 0) then
            eerr p "the arguments of a spawned call cannot suspend (#156)"
          let taskTy := Ty.struct (ctx.types.concurrencyName "task") [msRet]
          let rargs := env.coreArgs c targs
          let mut acc : Expr := .prim .userErr []
          for d in ds.reverse do
            let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
            let vars := env.coreVars d
            let X := vars.zipIdx.map fun ((_, t), i) =>
              Ty.param s!"$ext{i}" (match t with | .param _ k => k | _ => false)
            let view := if env.viewed.contains c then env.viewOf c d X else X.take rargs.length
            let atX := X.zipIdx.map fun (x, j) => (pinArg j, x)
            let pins := (X.zip (env.dispatchPins d)).filterMap fun (x, pin) =>
              pin.map fun t => (x, t.subst atX)
            let fields (n : String) (ts : List Ty) : Option (List Ty) :=
              if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
            let some mu := Ty.unifyEqs fields [] (view.zip rargs ++ pins) | continue
            let dargs := ((env.sparams.lookup d).getD []).map fun (n, _) =>
              (vars.findIdx? (·.1 == n)).map (X[·]!) |>.getD .void
            let some mu := env.refineComparable? mu (env.comparableArgs d dargs) | continue
            let name := s!"$spawnSelf{slot}"
            let self : Local := { name, slot, ty := .struct d (dargs.map (·.subst mu)), mutable := false }
            let unrefine := mu.filterMap fun (n, t) =>
              if ctx.dictVars.contains n && t.params.any (·.startsWith "$ext") then
                (env.tvars.lookup n).map (t, ·) else none
            let cctx := { ctx with
              locals := self :: (locs ++ ctx.locals).map (fun l => { l with ty := l.ty.subst mu }),
              types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst mu) }, unrefine }
            let rc ← elabSpawnDispatch cctx p d fname s!"{owner}.{m}" (.ident p name :: argIds.toList)
              (some (taskTy.subst mu))
            match rc.e with
            | .prim .userErr [] => continue -- factory discovery; no task or wait yet
            | _ => pure ()
            let some (.call fi (.local receiver :: values)) := Expr.inlineArgTemps rc.e
              | eerr p "internal: a spawn factory is not a dispatch call"
            if receiver != slot then eerr p "internal: a spawn factory changed its receiver"
            acc := .ite (.heap (.isTag [env.tagOf d]) [.local slot]) (.call fi (.local slot :: values)) acc
          let result ← fresh taskTy
          return ⟨pre.toList.foldr Expr.seq (.assign result acc), taskTy⟩
        let mut acc : Expr := .prim .userErr []   -- no option set: unreachable
        -- Supplied arguments have already been evaluated in caller order.
        -- Default forwarding leaves only those typed locals in the dispatch.
        if env.viewed.contains c then
          -- (#351) a receiver through views: one test per class below, a
          -- dispatch that opens the class's Verse Core type arguments,
          -- refined by its view (the receiver's are the interface's at the
          -- class's) and its pins (`Typed.dispatch_view`)
          let rargs := env.coreArgs c targs
          let mut emitted := false
          for d in ds.reverse do
            let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
            let e := clsOf fname
            let vars := env.coreVars d
            -- (each as comparable as the type parameter at its place)
            let X := vars.zipIdx.map fun ((_, t), i) =>
              Ty.param s!"$ext{i}" (match t with | .param _ k => k | _ => false)
            let view := env.viewOf c d X
            let atX := X.zipIdx.map fun (x, j) => (pinArg j, x)
            let pinEqs := (X.zip (env.dispatchPins d)).filterMap fun (x, pin) => match pin with
              | some pt => some (x, pt.subst atX)
              | none => none
            let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
              if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
            -- (no substitution relates them: no object of `d` is the receiver)
            -- (the opened ones bound to the reference's, not those to them:
            -- the code's own type parameters keep their names, as in a
            -- dispatch with no view, and errors name them)
            let some μF := Ty.unifyEqs coreFields [] (view.zip rargs ++ pinEqs) | continue
            let selfName := s!"$self{slot}"
            -- (the implementation's class or interface `e`, above `d`, at
            -- its places among the opened ones: a class's are a prefix of
            -- `d`'s, an interface's those its view gives; not through `d`'s
            -- own parameters, which a class that only inherits has no pins
            -- relating to them, `low(t, u) := class(both(t, []u))`)
            let eCore : List Ty := if env.viewed.contains e then env.viewOf e d X else X
            let eVars := env.coreVars e
            let eArgs := ((env.sparams.lookup e).getD []).map fun (v, _) =>
              match eVars.findIdx? (fun (x : String × Ty) => x.1 == v) with
              | some j => eCore.getD j Ty.void
              | none => Ty.void
            let some μF := env.refineComparable? μF (env.comparableArgs e eArgs) | continue
            let locsF := locs.map fun l => { l with ty := l.ty.subst μF }
            let selfL : Local := { name := selfName, slot,
                                   ty := .struct e (eArgs.map (·.subst μF)), mutable := false }
            let unrefine := μF.filterMap fun (x, t) =>
              if ctx.dictVars.contains x && t.params.any (·.startsWith "$ext") then
                (ctx.types.tvars.lookup x).map (t, ·)
              else none
            let ctx' := { ctx with
              locals := selfL :: (locsF ++ ctx.locals.map fun l => { l with ty := l.ty.subst μF }),
              types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μF) }, unrefine }
            let rc ← elabDefaultDispatch ctx' p fname (.ident mp selfName :: argIds.toList) bracket
              (some (msRet.subst μF))
            let rcE : Expr := match rc.e with
              | .seq (.ite (.prim .fail []) _ (.lit .void)) b => b
              | e => e
            -- (a dispatch through a view opens all of the class's type
            -- arguments: defaults with no type of their own at the
            -- declaration's, #209)
            let some (.call fi (.local s0 :: es)) := Expr.inlineArgTemps rcE
              | eerr p s!"cannot dispatch {m} through a view to class {d} yet when a named argument's default is computed (#351)"
            if s0 != slot then eerr p s!"internal error: a dispatch through a view to class {d} (#351)"
            acc := .ite (.heap (.isTag [env.tagOf d]) [.local slot]) (.call fi (.local slot :: es)) acc
            emitted := true
          if !emitted && ms.decides then acc := .prim .fail []
          let y ← fresh msRet
          let body ← if ms.suspends then withDeferMark ctx (.assign y acc) else pure (.assign y acc)
          return ⟨pre.toList.foldr Expr.seq body, msRet⟩
        if env.isRefClass c then
          -- a reference: one test of the object's class per implementation (#34)
          let mut groups : Array (String × Array String) := #[]
          for d in ds do
            let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
            match groups.findIdx? (·.1 == fname) with
            | some gi => groups := groups.modify gi fun (e', cls) => (e', cls.push d)
            | none => groups := groups.push (fname, #[d])
          let mut pinned := false
          let mut emitted := false
          for (fname, cls) in groups.toList.reverse do
            let e := clsOf fname
            -- (#142) the type arguments the classes fix that the receiver's
            -- may not have: matched against the receiver's, they refine the
            -- call, which `Typed.dispatch` types under that refinement
            let rargs := env.coreArgs c targs
            -- (#209) the type arguments that the tested classes have pins
            -- on beyond the receiver's are opened as fresh parameters, which
            -- the refinement binds (as the checker opens them, `openCount`:
            -- a test is of classes with the same pins)
            let eLen := (env.pinsOf e).length
            let extOf (pins : List (Option Ty)) : List Ty :=
              (List.range (pins.length - rargs.length)).map fun i => Ty.param s!"$ext{i}" false
            let needOf (pins : List (Option Ty)) :=
              let rx := rargs ++ extOf pins
              let atR := rx.zipIdx.map fun (r, j) => (pinArg j, r)
              (rx.zip pins).filterMap fun (a, pin) => match pin with
                | some pt => let pt := pt.subst atR; if a == pt then none else some (a, pt)
                | none => none
            -- (a generic <suspends> implementation at or above the receiver's
            -- class is called at the receiver's own type arguments, without
            -- the refinement: its frame is made by a call typed without it)
            let plainSusp := ms.suspends && env.isSub c e && !((ctx.sig? fname).map (·.tparams.isEmpty)).getD true
            -- (an implementation at or above the receiver's class is called
            -- at the receiver's type arguments, which it takes as they are)
            -- (#351: also one above it, the default of an interface referred
            -- to through views, when the receiver does not convert to it: a
            -- class's pins refine it, as Verse Core's are, `dispatchPins`)
            let viewedAbove := env.isSub c e && env.viewed.contains e && !env.viewed.contains c && c != e
            if !plainSusp && (!env.isSub c e || viewedAbove) && cls.any fun d =>
                !(needOf (env.dispatchPins d)).isEmpty || eLen > rargs.length then
              -- one test per set of pins among the classes using `e`'s
              -- implementation: `Typed.dispatch` refines by the pins all the
              -- tested classes share, which may fix more than `e`'s (and it
              -- takes the receiver as narrowed by the test, so no temporary
              -- of `e`'s type, which might have no initial value)
              let mut parts : Array (List (Option Ty) × Array String) := #[]
              for d in cls do
                -- (by their Verse Core pins, which the rule compares, #351)
                let key := env.dispatchPins d
                match parts.findIdx? (·.1 == key) with
                | some pi => parts := parts.modify pi fun (k, ds') => (k, ds'.push d)
                | none => parts := parts.push (key, #[d])
              for (pins, part) in parts.toList.reverse do
                -- (whether an object of `part` can be the receiver, by
                -- Verse's types)
                if (Ty.unifyEqs (fun _ _ => none) [] (needOf pins)).isNone then continue
                -- (pins that relate the receiver's type arguments to ones
                -- past those of `e`, whose implementation is called: they
                -- would instantiate `e`'s type parameters with what the
                -- dispatch opens; so, where `e` takes the receiver's type
                -- arguments as they are (no pins of its own on them, and no
                -- more of them), no refinement, and `e`'s implementation
                -- takes the receiver as it is; elsewhere the refinement
                -- below, whose hidden arguments for `e`'s implementation are
                -- built from the caller's own type parameters, which the
                -- refinement binds to what it opens, `Ctx.unrefine`, #209)
                -- (unless the implementation takes no values of type arguments,
                -- reading them from its receiver, `Sig.selfTps`)
                let calleeDicts := ((ctx.sig? fname).map (·.ndicts)).getD 0
                -- (#530: not an interface's default seen through views, which
                -- a test's temporary of its type cannot take as it is: a
                -- class whose closed view the receiver's do not give, `c1`'s
                -- `string` for `i1(u)`, is one only under the refinement)
                if calleeDicts != 0 && !viewedAbove &&
                    !VTy.pinsBelow (env.lowerPins (pins.take (max eLen rargs.length))) (max eLen rargs.length) &&
                    (needOf (env.corePins e)).isEmpty && eLen ≤ rargs.length then
                  let argsE := argsAt e
                  let some μ := env.refineComparable? [] (env.comparableArgs e argsE) | continue
                  let ty := Ty.struct e (argsE.map (·.subst μ))
                  let sd ← fresh ty
                  let ctx' := { ctx with
                    locals := { name := s!"$self{sd}", slot := sd, ty, mutable := false } ::
                      ((locs ++ ctx.locals).map fun l => { l with ty := l.ty.subst μ }),
                    types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μ) } }
                  let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
                  acc := .ite (.assign sd (.heap (.isTag (part.toList.map env.tagOf)) [.local slot]))
                    (← coerce p rc msRet) acc
                  emitted := true
                  continue
                -- (no instance of the receiver's type arguments agrees with
                -- the pins: no object of `part` is the receiver)
                -- (whether an object of `part` can be the receiver, by
                -- Verse's types; the refinement, as Verse Core has it: a
                -- value struct by its fields, #209)
                if (Ty.unifyEqs (fun _ _ => none) [] (needOf pins)).isNone then continue
                let coreFields (n : String) (ts : List Ty) : Option (List Ty) :=
                  if env.classes.contains n then none else some ((env.fields n ts).map (·.2.1))
                let some μF := Ty.unifyEqs coreFields [] (needOf pins) | continue
                let selfName := s!"$self{slot}"
                let argsE := if env.isSub c e then argsAt e else env.argsBelow c targs e (extOf pins)
                let some μF := env.refineComparable? μF (env.comparableArgs e argsE) | continue
                let locsF := locs.map fun l => { l with ty := l.ty.subst μF }
                let selfL : Local := { name := selfName, slot, ty := .struct e (argsE.map (·.subst μF)), mutable := false }
                -- (the caller's type parameters the refinement binds to
                -- types that mention opened ones, for the hidden arguments
                -- of a generic implementation, #209)
                let unrefine := μF.filterMap fun (x, t) =>
                  if ctx.dictVars.contains x && t.params.any (·.startsWith "$ext") then
                    (ctx.types.tvars.lookup x).map (t, ·)
                  else none
                let ctx' := { ctx with
                  locals := selfL :: (locsF ++ ctx.locals.map fun l => { l with ty := l.ty.subst μF }),
                  types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μF) }, unrefine }
                let rc ← elabDefaultDispatch ctx' p fname (.ident mp selfName :: argIds.toList) bracket
                  (some (msRet.subst μF))
                -- (named arguments go through temporaries: put their values
                -- in the call, which must have the rule's shape)
                -- (a suspends call carries the defers active at it, which
                -- go around the whole dispatch instead)
                let rcE : Expr := match rc.e with
                  | .seq (.ite (.prim .fail []) _ (.lit .void)) b => b
                  | e => e
                let some (.call fi (.local s0 :: es)) := Expr.inlineArgTemps rcE
                  | eerr p s!"cannot dispatch {m} to class {e}, which fixes type arguments of {c}, when a named argument's default is computed (#142)"
                if s0 != slot then eerr p s!"cannot dispatch {m} to class {e}, which fixes type arguments of {c} (#142)"
                acc := .ite (.heap (.isTag (part.toList.map env.tagOf)) [.local slot]) (.call fi (.local slot :: es)) acc
                pinned := true
                emitted := true
              continue
            let argsE := argsAt e
            let some μ := env.refineComparable? [] (env.comparableArgs e argsE) | continue
            let ty := Ty.struct e (argsE.map (·.subst μ))
            let sd ← fresh ty
            let ctx' := { ctx with
              locals := { name := s!"$self{sd}", slot := sd, ty, mutable := false } ::
                ((locs ++ ctx.locals).map fun l => { l with ty := l.ty.subst μ }),
              types := { env with tvars := env.tvars.map fun (n, t) => (n, t.subst μ) } }
            let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
            acc := .ite (.assign sd (.heap (.isTag (cls.toList.map env.tagOf)) [.local slot]))
              (← coerce p rc msRet) acc
            emitted := true
          -- (no class can be the receiver: the call cannot run; a failable
          -- one still fails, for the failure checks)
          if !emitted && ms.decides then acc := .prim .fail []
          if pinned then
            -- (checked against the method's result type, as the refined
            -- calls need an expected type)
            let y ← fresh msRet
            let body ← if ms.suspends then withDeferMark ctx (.assign y acc) else pure (.assign y acc)
            return ⟨pre.toList.foldr Expr.seq body, msRet⟩
          return ⟨pre.toList.foldr Expr.seq acc, msRet⟩
        for (d, j) in (ds.zip (List.range ds.length)).reverse do
          let some fname := ctx.implFor? d root m | eerr p s!"class {d} does not implement '{m}'"
          let td ← fresh (classRepTy env d)
          let sd ← fresh (.struct d [])
          let ctx' := { ctx with locals := { name := s!"$self{sd}", slot := sd, ty := .struct d [], mutable := false } :: (locs ++ ctx.locals) }
          let rc ← elabApp ctx' p (.ident mp fname) (.ident mp s!"$self{sd}" :: argIds.toList) bracket exp
          acc := .ite (.assign td (.prim .query [.prim (.tupGet j) [.local slot]]))
            (.seq (.assign sd (classWrap env d d (.local td))) (← coerce p rc msRet)) acc
        let y ← fresh msRet
        return ⟨pre.toList.foldr Expr.seq (.assign y acc), msRet⟩
      else if (ctx.types.fields c targs).any (·.1 == m) then
        -- `S.F[i]`, `S.F(k)`: a field, indexed
        indexLike f (← elabMember ctx p r m)
      else if ctx.types.classes.contains c then eerr p s!"class {c} has no method '{m}'"
      else eerr p s!"struct {c} has no field '{m}' (structs have no methods)"
    | _ => elabMethod ctx p r m args bracket
  | _ => indexLike f (← elabE ctx f none)

end OpenVerse.Front
