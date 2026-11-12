/- Elaboration statement; public declarations retain OpenVerse.Front names. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse
set_option maxHeartbeats 800000 in
/-- A statement: like `elabE`, but a declaration extends the scope. Also
    enforces the failure discipline. -/
partial def elabStmtWith (elabE : Ctx → SExpr → Option Ty → EM R) (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM (R × Ctx) := do
  let (r, ctx') ← match se with
    | .decl p n sty isVar rhs => do
      let (rhs, copied, envInit) := match rhs with
        | .app _ (.ident _ "$refineCopyIn") [e@(.ident _ source)] false => (e, (ctx.lookup source).bind (·.storage), false)
        | .app _ (.ident _ "$forEnvInit") [e@(.ident _ _)] false => (e, none, true)
        | e => (e, none, false)
      if let .app dp (.ident _ "$defer") _ _ := rhs then eerr dp "defer: is a statement: it has no value"
      checkNewLocal ctx p n
      let ty? ← sty.mapM (resolveTy ctx.types p)
      let r ← elabE ctx rhs ty?
      let ty := ty?.getD r.ty
      if ty == .never then
        eerr p (if n.startsWith "$" then "cannot infer the type of this clause's value" else s!"cannot infer the type of '{n}'")
      let e ← coerce p r ty
      let slot ← fresh ty
      let storage := copied.orElse (fun _ => ctx.resumeStorage.lookup n) |>.orElse fun _ => if isVar && ctx.suspends then
        some { frame := ctx.frameName, name := s!"{p.file}:{p.line}:{p.col}:{n}", args := ctx.frameArgs } else none
      if let some s := storage then
        modify fun st => { st with frameSlots := st.frameSlots ++ [(slot, s)] }
      if envInit then
        if let .local result := e then
          modify fun st => { st with frameCopies := st.frameCopies ++ [{ target := slot, result }] }
      let binding : Local := {
        name := n, slot, ty, mutable := isVar, storage
        typeValue := ctx.isTypeValue rhs }
      pure (⟨.assign slot e, ty⟩, { ctx with locals := binding :: ctx.locals })
    | .app _ (.ident _ "$inlineScope") [.str _ [.text name]] false =>
      pure (⟨.lit .void, .void⟩, { ctx with inlineScopes := name :: ctx.inlineScopes })
    | .app _ (.ident _ "$inlineScopeEnd") [] false =>
      pure (⟨.lit .void, .void⟩, { ctx with inlineScopes := ctx.inlineScopes.drop 1 })
    | .app p (.ident _ "$methodParams") [.ident _ receiver, .str _ [.text method], .block _ ownTypes, .block _ args] _ => do
      let aliases ← ownTypes.mapM fun
        | .decl _ _ (some (.name n)) _ _ => pure n
        | _ => eerr p "internal: a method's type parameter"
      if aliases.all fun n => (ctx.types.tvars.lookup n).isSome then
        pure (⟨.lit .void, .void⟩, ctx)
      else
        let some receiverLocal := ctx.lookup receiver | eerr p "internal: missing method receiver"
        let .struct c _ := receiverLocal.ty | eerr p "method receiver is not a class or interface"
        let some owner := ctx.methodDecl? c method | eerr p s!"{c} has no method {method}"
        let root := (ctx.rootsOf c method).headD owner
        let implementations := ((ctx.types.concreteBelow c).map (ctx.implFor? · root method)).eraseDups
        let [some fname] := implementations
          | eerr p s!"cannot infer the type parameters of {method} from the arguments of this call"
        let some member := ctx.sig? fname | eerr p "internal: missing method declaration"
        -- Interface defaults may have been copied onto a concrete class
        -- after method extraction. Their generated function belongs to the
        -- original interface, whose parameters its receiver still supplies.
        let cls := member.scope.getD (fname.splitOn ".").head!
        if !ctx.types.isSub c cls then
          eerr p s!"cannot infer the type parameters of {method} from the arguments of this call"
        -- The member's checking stub has erased defaults. The generated
        -- implementation function retains their bodies and lexical scope.
        let implementation := Choice.methodFnName cls method
        let some sig := ctx.sig? implementation | eerr p "internal: missing method implementation"
        let saved ← get
        let packet ← elabGenericCallWith elabE { ctx with typeOnly := true, callInstanceProbe := some implementation }
          p sig (.ident p receiver :: args) none
        restoreConstructProbe ctx saved
        let .tup types := packet.ty | eerr p "internal: a method argument type packet"
        let own := types.drop ((ctx.types.sparams.lookup cls).getD []).length
        pure (⟨.lit .void, .void⟩, { ctx with types := { ctx.types with tvars := ctx.types.tvars ++ aliases.zip own } })
    | .app p (.ident _ "$methodType") [.ident _ receiver, .str _ [.text method], .block _ ownTypes] false => do
      let some receiverLocal := ctx.lookup receiver | eerr p "internal: missing method receiver"
      let .struct c args := receiverLocal.ty | eerr p "method receiver is not a class or interface"
      let some owner := ctx.methodDecl? c method | eerr p s!"{c} has no method {method}"
      let some sg := ctx.sig? s!"{owner}.{method}" | eerr p "internal: missing method declaration"
      let names := ((ctx.types.sparams.lookup owner).getD []).map (·.1)
      let types ← ownTypes.mapM fun
        | .decl q _ (some t) _ _ => resolveTy ctx.types q t
        | _ => eerr p "internal: a method's type argument"
      let own := (sg.tparams.drop names.length).map (·.1)
      let result := sg.ret.subst (names.zip (ctx.types.upArgs c args owner) ++ own.zip types)
      pure (⟨.lit .void, .void⟩, { ctx with types := { ctx.types with tvars := (receiver, result) :: ctx.types.tvars } })
    | .app _ (.ident _ "$declNames") ns false => do
      -- (#283) the names a block whose choice is lifted binds (renamed for
      -- the place): not in scope where the block is, as for its own
      for n in ns do
        if let .ident q n := n then checkNewLocal ctx q n
      pure (⟨.lit .void, .void⟩, ctx)
    | .app p (.ident _ "$freeNames") (.ident _ f :: ns) false => do
      -- (#283) the names an inlined body uses from outside: not bound
      -- here, where they would mean something else
      for n in ns.filterMap (fun | .ident _ n => some n | _ => none) do
        let member := match ctx.selfClass with
          | some c => ctx.hasMethod c n || (ctx.types.fields c).any (·.1 == n)
          | none => false
        if (ctx.lookup n).isSome || member then
          eerr p (s!"{f} has several values and uses {n}, which is also the name of a " ++
            s!"{if member then "member of Self" else "local"} here: rename one, as {f}'s body is inlined here, " ++
            s!"where {n} would mean that (#235, #283)")
      pure (⟨.lit .void, .void⟩, ctx)
    | .app p (.ident _ "$params") (.block _ decls :: tps) false => do
      -- (#235) an inlined generic call's parameters, bound together: its
      -- type arguments inferred from the arguments as at a call (each
      -- checked against its parameter's type once the type parameters it
      -- mentions are bound, else inferring them; `false`, `array{}` and
      -- `map{}` last), then named for the written types after
      let fname := match tps with | .ident _ f :: _ => f | _ => ""
      let parameters ← (tps.drop 1).mapM fun marker => do
        match TParam.ofMarker marker with
        | .ok tp => pure tp
        | .error message => throw message
      match UpperBounds.checkParams parameters with
      | .error message => throw message
      | .ok _ => pure ()
      let cons := parameters.map fun tp => (tp.name, tp.constraint)
      let formal ← resolveTParams ctx.types parameters
      let names := cons.map (·.1)
      -- (as messages show them: the type parameters' own names)
      let shown (t : Ty) : String :=
        (t.subst (names.map fun n => (n, Ty.param ((n.dropWhile (· != '_')).drop 1).toString false))).show
      let penv := formal.env ctx.types
      let raw ← decls.mapM fun
        | .decl q x (some sty) v a => pure (q, x, sty, v, a)
        | d => eerr d.pos "internal: a $params clause (#235)"
      let inputs : List SParam := raw.map fun (_, name, ty, _, a) =>
        { name, ty, typeValue := ctx.isTypeValue a }
      let (types, _) ← resolveSignatureTypes penv p inputs (.name "void") fname
      let items := (raw.zip types).map fun ((q, x, _, v, a), ty) => (q, x, v, a, ty)
      let contextual := (← items.mapM (fun (_, _, _, a, _) => argNeedsTypeWith elabE ctx a)).toArray
      let mut σ : List (String × Ty) := []
      let mut done : Array (Option (Expr × Ty)) := Array.replicate items.length none
      let mut deferred : Array Bool := contextual
      for pass in [0, 1] do
        for ((q, _, _, a, t0), i) in items.zipIdx do
          if (pass == 0) == deferred[i]! then continue
          let t := t0.subst σ
          if t.params.any names.contains then
            if contextual[i]! then eerr q s!"cannot infer the type parameters of {fname} from the arguments of this call"
            let r ← elabE ctx a none
            match t.matchArg ctx.types σ r.ty with
            | some σ' =>
              σ := σ'.filter fun (v, _) => names.contains v
              if !formal.bounds.isEmpty then
                let some inferred := SubtypeEvidence.infer ctx.evidenceEnv formal.bounds σ
                  | eerr q "cannot infer consistent nominal bound arguments"
                σ := inferred
              let t' := t.subst σ
              if t'.params.any names.contains then
                if pass == 0 then deferred := deferred.set! i true
                else eerr q s!"cannot infer the type parameters of {fname} from this argument"
              else done := done.set! i (some (← coerce q r t', t'))
            | none => eerr q s!"expected {shown t}, found {r.ty.show} (in a call of {fname})"
          else
            done := done.set! i (some (← coerce q (← elabE ctx a (some t)) t, t))
      -- (a comparable type parameter's type argument must be comparable,
      -- as at a call)
      for (n, c) in cons do
        if c == "comparable" then
          if let some t := σ.lookup n then
            if !(isComparable ctx.types t) then
              eerr p (notComparable ctx.types t s!"{fname}'s type argument for {((n.dropWhile (· != '_')).drop 1).toString}")
      let mut code : Expr := .lit .void
      let mut c := ctx
      for ((q, x, v, a, _), d) in items.zip done.toList do
        let some (e, t) := d | eerr q s!"cannot infer the type parameters of {fname} from the arguments of this call"
        checkNewLocal c q x
        let slot ← fresh t
        code := .seq code (.assign slot e)
        c := { c with locals := { name := x, slot, ty := t, mutable := v, typeValue := ctx.isTypeValue a } :: c.locals }
      if !formal.bounds.isEmpty then
        σ ← c.checkInlineInstance p formal σ ((ctx.sig? fname).map (·.named.isEmpty) |>.getD true)
      pure (⟨.seq code (.lit .void), .void⟩, { c with types := { c.types with tvars := c.types.tvars ++ σ } })
    | .app p (.ident _ "$defaults") (.block _ decls :: tps) false => do
      -- (#283) the defaults an inlined generic call omits, after its
      -- `$params`, as at a call: in order, each seeing the parameters
      -- before it, at its parameter's type, or, when that mentions a type
      -- parameter nothing else determined, giving it its type argument;
      -- then every type parameter must have one
      let fname := Choice.shownFnName (match tps with | .ident _ f :: _ => f | _ => "")
      let parameters ← (tps.drop 1).mapM fun marker => do
        match TParam.ofMarker marker with
        | .ok tp => pure tp
        | .error message => throw message
      match UpperBounds.checkParams parameters with
      | .error message => throw message
      | .ok _ => pure ()
      let cons := parameters.map fun tp => (tp.name, tp.constraint)
      let formal ← resolveTParams ctx.types parameters
      let shownTp (n : String) : String := ((n.dropWhile (· != '_')).drop 1).toString
      let open_ := cons.filter fun (n, _) => (ctx.types.tvars.lookup n).isNone
      let names := open_.map (·.1)
      let known := formal.params.filterMap fun (n, _) => (ctx.types.tvars.lookup n).map (n, ·)
      let penv : TyEnv := { ctx.types with
        tvars := ctx.types.tvars ++ open_.map fun (n, _) => (n, Ty.param n ((formal.params.lookup n).getD false))
        boundFacts := ctx.types.boundFacts ++ formal.bounds.map (fun bound =>
          let bound := bound.subst known
          (bound.base, bound.derived)) }
      let shown (t : Ty) : String := (t.subst (names.map fun n => (n, Ty.param (shownTp n) false))).show
      let fromContext : SExpr → Bool
        | .app _ (.ident _ "$paramDefault") [_, _, _, .ident _ "false"] false
        | .app _ (.ident _ "$paramDefault") [_, _, _, .arrayLit _ []] false
        | .app _ (.ident _ "$paramDefault") [_, _, _, .mapLit _ []] false => true
        | _ => false
      let mut σ : List (String × Ty) := []
      let mut code : Expr := .lit .void
      let mut c := ctx
      for d in decls do
        let .decl q x (some sty) v a := d | eerr d.pos "internal: a $defaults clause (#283)"
        let t := (← resolveTy penv q sty).subst σ
        let mut e : Expr := .lit .void
        let mut t' := t
        if t.params.any names.contains then
          if fromContext a then
            eerr p s!"cannot infer type parameter {shownTp ((t.params.filter names.contains).headD "t")} of {fname} from the arguments of this call"
          let r ← elabE c a none
          match t.matchArg ctx.types σ r.ty with
          | some σ' =>
            σ := σ'.filter fun (n, _) => names.contains n
            t' := t.subst σ
            e ← coerce q r t'
          | none => eerr q s!"expected {shown t}, found {r.ty.show} (the default of a parameter of {fname})"
        else
          e ← coerce q (← elabE c a (some t)) t
        checkNewLocal c q x
        let slot ← fresh t'
        code := .seq code (.assign slot e)
        c := { c with locals := { name := x, slot, ty := t', mutable := v, typeValue := c.isTypeValue a } :: c.locals }
      if !formal.bounds.isEmpty then
        let inferred ← c.checkInlineInstance p formal (known ++ σ)
        σ := inferred.filter fun (n, _) => names.contains n
      for (n, k) in open_ do
        match σ.lookup n with
        | none => eerr p s!"cannot infer type parameter {shownTp n} of {fname} from the arguments of this call"
        | some t =>
          if k == "comparable" && !(isComparable ctx.types t) then
            eerr p (notComparable ctx.types t s!"{fname}'s type argument for {shownTp n}")
      pure (⟨.seq code (.lit .void), .void⟩, { c with types := { c.types with tvars := c.types.tvars ++ σ } })
    | _ => do pure (← elabE ctx se exp, ctx)
  if !ctx.canFail && (r.e.mayFail ctx.sigProg) then
    eerr se.pos ("this expression can fail, but it is not in a failure context (an if " ++
      "condition, a for clause, option{…}, logic{…}, not, the left of or, or a <decides> function)")
  return (r, ctx')

end OpenVerse.Front
