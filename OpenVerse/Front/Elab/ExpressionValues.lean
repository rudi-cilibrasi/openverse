/- A contiguous expression-handler stage; fallthrough preserves source pattern order. -/
import OpenVerse.Front.Elab.Control

namespace OpenVerse.Front
open OpenVerse
set_option maxHeartbeats 800000 in
partial def elabExprValuesWith
    (elabE : Ctx → SExpr → Option Ty → EM R)
    (elabBlock : Ctx → List SExpr → Option Ty → EM (R × Ctx))
    (elabApp : Ctx → Pos → SExpr → List SExpr → Bool → Option Ty → EM R)
    (ratCall : Ctx → Pos → String → List Expr → EM Expr)
    (elabCmp : Ctx → Pos → SExpr → List (String × SExpr) → EM R)
    (elabMember : Ctx → Pos → R → String → (exp : optParam (Option Ty) none) → EM R)
    (elabConstruct : Ctx → Pos → String → List STy → List SExpr → Option Ty → EM R)
    (elabMapLit : Ctx → Pos → List (SExpr × SExpr) → Option Ty → EM R)
    (ctx : Ctx) (se : SExpr) (exp : Option Ty) : EM R := do
  -- (an operand of a failure context that is a cast, `not T[X]`, or has one
  -- in it: the block of it, where a cast that refines takes the rest as
  -- its branch)
  let operand (c : Ctx) (e : SExpr) (exp : Option Ty) : EM R := do
    if (Refine.castClause? e).isSome || (c.canFail && !(Refine.castsIn c.types.classes.contains e).isEmpty) then
      return (← elabBlock c [e] exp).1
    elabE c e exp
  match se with
  | .app p f args bracket => do
    let r ← elabApp ctx p f args bracket exp
    -- (#515) the calls of a failure context, for `--signal-no-rollback`
    noteFailCalls ctx p "call" r.e
    return r
  | .member p (.ident _ n) m =>
    if n == "(super:)" then
      eerr p s!"(super:){m} cannot be used as a value: call it with (super:){m}(…), or name a method that calls it"
    match ctx.lookup n, ctx.types.enums.lookup n with
    | none, some vals =>
      -- `color.Red`: an enumerator
      match vals.idxOf? m with
      | some k => return ⟨.lit (Value.ofInt k), .enum n⟩
      | none => eerr p s!"enum {n} has no value '{m}'"
    | _, _ => elabMember ctx p (← elabE ctx (.ident p n) none) m exp
  | .member p e m => elabMember ctx p (← elabE ctx e none) m exp
  | .construct p name targs args => do
    let r ← elabConstruct ctx p name targs args exp
    -- (#515: a construction calls its classes' `block:`s, and constructor
    -- functions)
    noteFailCalls ctx p "construction" r.e
    return r
  | .mapLit p entries => elabMapLit ctx p entries exp
  | .structDef p _ _ _ | .enumDef p _ _ | .refineDef p _ _ _ | .typeAlias p _ _ =>
    eerr p "struct, enum and type definitions must be at the top level"
  | .query p e =>
    let r ← elabE ctx e none
    let r ← elabContainerReceiverWith elabE ctx p r (fun
      | .opt _ | .logic => true
      | _ => false) "query"
    match r.ty with
    | .opt t => return ⟨.prim .query [r.e], t⟩
    | .logic => return ⟨.prim .query [r.e], .logic⟩
    | t => eerr p s!"'?' needs an option or logic, found {t.show}"
  | .neg p e =>
    -- The expected numeric type as a hint, as in `-Id(2.5)`.
    let hint : Option Ty := match exp with
      | some .float => some .float
      | some .rational => some .rational
      | _ => none
    let r0 ← elabArithmeticOperandWith elabE ctx p (← elabE ctx e hint) "negation"
    let r := widenR ctx.types r0
    -- (the negation of a refined value is of an expected refinement whose
    -- interval holds the flipped one, #143)
    if let (.refine n, some (.refine m)) := (r0.ty, exp) then
      if let (some (bn, cn), some (bm, cm)) := (ctx.types.refines.lookup n, ctx.types.refines.lookup m) then
        if bn == bm && intervalWithin (intervalNeg (refineInterval cn)) (refineInterval cm) then
          return ⟨.prim (if bn == .float then .fneg else .neg) [r.e], .refine m⟩
    if r.ty == .float then return litAt ctx.types exp ⟨.prim .fneg [r.e], .float⟩
    if r.ty == .rational then
      let t ← fresh .rational
      return ⟨.seq (.assign t r.e) (.prim .mkTup
        [.prim .neg [.prim (.tupGet 0) [.local t]], .prim (.tupGet 1) [.local t]]), .rational⟩
    if r.ty != .int then eerr p s!"unary '-' needs an int, rational or float, found {r.ty.show}"
    return litAt ctx.types exp ⟨.prim .neg [r.e], .int⟩
  | .notE p e =>
    -- (with a choice, its first success, #208)
    let e := (Choice.takeFirst? e (choiceOrder ctx)).getD e
    let r ← operand { ctx with canFail := true, inTaking := true } e none
    -- (a failure context of an expression that cannot fail, as an `if`'s
    -- condition and `logic{…}`: `not` of one always fails)
    if !(r.e.mayFail ctx.sigProg) && (← ctx.failabilityKnown) then
      eerr p "the operand of not cannot fail (Verse requires a failable one: not of it always fails)"
    return ⟨Expr.notE (← inferable r), .void⟩
  | .bin p "/" a b =>
    -- `X / Y` on ints: a rational, failing when `Y = 0` (#116)
    let ra := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p (← elabE ctx a none) "division")
    let rb := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p
      (← elabE ctx b (if ra.ty == .float then some .float else none)) "division")
    -- (on floats, IEEE division: by zero an infinity or NaN, #127)
    if ra.ty == .float && rb.ty == .float then return ⟨p2 .fdiv ra.e rb.e, .float⟩
    if ra.ty == .float || rb.ty == .float then
      eerr p s!"no operator '/' for {ra.ty.show} and {rb.ty.show} (an int is not a float: write X * 1.0)"
    if ra.ty == .rational || rb.ty == .rational then
      return ⟨← rationalBinary p .quotient ra rb, .rational⟩
    let es := [← coerce a.pos ra .int, ← coerce b.pos rb .int]
    return ⟨← ratCall ctx p "$ratMake" es, .rational⟩
  | .bin p op a b =>
    let operation := s!"operator '{op}'"
    let ra := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p
      (← elabE ctx a none) operation (op == "+"))
    let rb ← match op, ra.ty with
      | "+", .arr _ =>
        -- (an array of other classes, to join, #67)
        if ctx.retries ≥ 3 then elabE ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (elabE c2 b (some ra.ty)) fun _ => elabE c2 b none
      | "+", .int | "-", .int | "*", .int | "*", .float =>
        -- Mixed rational operators and int-times-float can need the
        -- right operand's own type instead of the left operand's hint.
        if ctx.retries ≥ 3 then elabE ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (elabE c2 b (some ra.ty)) fun _ => elabE c2 b none
      | _, _ => elabE ctx b (some ra.ty)
    let rb := widenR ctx.types (← elabArithmeticOperandWith elabE ctx p rb operation (op == "+"))
    if ra.ty == .rational || rb.ty == .rational then
      let prim ← match op with
        | "+" => pure Prim.add | "-" => pure Prim.sub | "*" => pure Prim.mul
        | _ => eerr p s!"no operator '{op}' for {ra.ty.show} and {rb.ty.show}"
      return ⟨← rationalBinary p prim ra rb, .rational⟩
    match op, ra.ty, rb.ty with
    | "+", .int, .int => return ⟨p2 .add ra.e rb.e, .int⟩
    | "-", .int, .int => return ⟨p2 .sub ra.e rb.e, .int⟩
    | "*", .int, .int => return ⟨p2 .mul ra.e rb.e, .int⟩
    -- floats (#127): no implicit int to float, except in `*` (`Count * 1.0`)
    | "+", .float, .float => return ⟨p2 .fadd ra.e rb.e, .float⟩
    | "-", .float, .float => return ⟨p2 .fsub ra.e rb.e, .float⟩
    | "*", .float, .float => return ⟨p2 .fmul ra.e rb.e, .float⟩
    | "*", .int, .float => return ⟨p2 .fmul (.prim .fofInt [ra.e]) rb.e, .float⟩
    | "*", .float, .int => return ⟨p2 .fmul ra.e (.prim .fofInt [rb.e]), .float⟩
    | "+", .arr t, .arr u =>
      if t == u then return ⟨p2 .concat ra.e rb.e, .arr t⟩
      -- arrays of classes concatenate at a common supertype (#32)
      match joinTy (← get).env (.arr t) (.arr u) exp with
      | some jt => return ⟨p2 .concat (← coerce p ra jt) (← coerce p rb jt), jt⟩
      | none =>
        if let some jt := SubtypeEvidence.joinView? ctx.types ctx.evidenceTypes [ra.ty, rb.ty] exp then
          return ⟨p2 .concat (← elabArgumentCoerceWith elabE ctx p ra jt)
            (← elabArgumentCoerceWith elabE ctx p rb jt), jt⟩
        eerr p s!"cannot concatenate {ra.ty.show} and {rb.ty.show}"
    | _, ta, tb => eerr p s!"no operator '{op}' for {ta.show} and {tb.show}"
  | .cmp p a rest => elabCmp ctx p a rest
  | .andE _ a b =>
    -- the whole `and` is a scope of its own, a block of `a` then `b`: names
    -- defined in `a` are visible in `b`, and names from neither side escape
    -- the `and` (Book of Verse ch. 7: "`e0 and e1` evaluates the entire
    -- expression in a new lexical scope"; ch. 1: "Variable bindings do not
    -- escape from logical operations")
    return (← elabBlock ctx [a, b] exp).1
  | .orE p a b =>
    let a := (Choice.takeFirst? a (choiceOrder ctx)).getD a
    let ra ← operand { ctx with canFail := true, inTaking := true } a exp
    let rb ← match exp with
      | some _ => operand ctx b exp
      | none =>
        if ctx.retries ≥ 3 then operand ctx b (some ra.ty)
        else
          let c2 := { ctx with retries := ctx.retries + 1 }
          tryCatch (operand c2 b (some ra.ty)) fun _ => operand c2 b none
    let ty ← join p ra.ty rb.ty exp
    let t ← fresh ty
    return ⟨Expr.orE t (← coerce p ra ty) (← coerce p rb ty), ty⟩
  | .range p _ _ => eerr p "a range a..b can only be the source of a for clause"
  | .tuple _ [] => return ⟨.lit .void, .void⟩
  | .tuple _ es =>
    let exps : List (Option Ty) := match exp with
      | some (.tup ts) => if ts.length == es.length then ts.map some else es.map fun _ => none
      -- (a tuple where an array is expected becomes one: its elements at
      -- the element type)
      | some (.arr t) => es.map fun _ => some t
      | _ => es.map fun _ => none
    let rs ← (es.zip exps).mapM fun (e, t) => elabE ctx e t
    -- (an element that never gives a value, `return e`, `break`, `Err()`,
    -- has no type of its own in Verse Core, where a tuple whose type is
    -- inferred, as `not`'s operand is, needs one: without an expected type,
    -- it is followed by `void`, the type `never` stands for there, #285;
    -- with one, it is checked against it, as it has every type)
    let elems := (rs.zip exps).map fun (r, t) => match r.ty, t with
      | .never, none => Expr.seq r.e (.lit .void)
      | _, _ => r.e
    return ⟨.prim .mkTup elems, .tup (rs.map (·.ty))⟩
  | .block _ ss =>
    let (r, _) ← elabBlock ctx ss exp
    return r
  | .arrayLit p es =>
    let elemExp : Option Ty := match exp with
      | some (.arr t) => some t
      | _ => none
    match es with
    | [] => match elemExp with
      | some t => return ⟨.lit Value.emptyArray, .arr t⟩
      | none => eerr p "the type of an empty array{} must be given (e.g. X:[]int = array{})"
    | e :: rest =>
      let r ← elabE ctx e elemExp
      let t := elemExp.getD r.ty
      let rs ← rest.mapM fun e' => elabE ctx e' (some t)
      let all := (e :: rest).zip (r :: rs)
      -- the expected element type (or the first's), when every element
      -- converts to it; else the join of their types (classes at a common
      -- supertype, #67), with no element elaborated again
      match ← tryCatch (some <$> all.mapM fun (e', x) => coerce e'.pos x t) (fun _ => pure none) with
      -- (elements that never give a value, without an expected type: each
      -- followed by `void`, the type `never` stands for, as a tuple's, #285)
      | some es => return ⟨.prim .mkArr (if t == .never && elemExp.isNone then es.map (.seq · (.lit .void)) else es), .arr t⟩
      | none =>
        let jt ← (rest.zip rs).foldlM (fun acc ((e', x) : SExpr × R) => do
            match joinTy (← get).env acc x.ty elemExp with
            | some j => pure j
            | none =>
              if (elemExp.isNone || elemExp == some .any) && !ambiguousJoin (← get).env acc x.ty then
                pure .any
              else eerr e'.pos s!"the elements of this array have different types: {acc.show} and {x.ty.show}") r.ty
        let es ← all.mapM fun (e', x) => coerce e'.pos x jt
        -- (an element that never gives a value, joined with others, without
        -- an expected type: into a temporary of the joined type, so that the
        -- array's type can be inferred, #297)
        let es ← if elemExp.isSome then pure es else (es.zip all).mapM fun (e, (_, x)) => do
          if x.ty != .never then return e
          let t ← modifyGet fun s => (s.nslots, { s with nslots := s.nslots + 1, slotTys := s.slotTys.push jt })
          return Expr.assign t e
        return ⟨.prim .mkArr es, .arr jt⟩
  | .optionLit _ e =>
    let e := (Choice.takeFirst? e (choiceOrder ctx)).getD e
    let inner : Option Ty := match exp with
      | some (.opt t) => some t
      | _ => none
    let r ← operand { ctx with canFail := true, inTaking := true } e inner
    -- an expression that cannot fail needs no failure context (and no
    -- saved state to roll back to: the interpreter's heap is not copied)
    -- (one that never gives a value, without an expected type: followed by
    -- `void`, the type `never` stands for in Verse Core, as in a tuple, #290)
    if !(r.e.mayFail ctx.sigProg) then
      let e := if r.ty == .never && inner.isNone then Expr.seq r.e (.lit .void) else r.e
      return ⟨.prim .mkSome [e], .opt r.ty⟩
    let t ← fresh r.ty
    return ⟨Expr.optionE t r.e, .opt r.ty⟩
  | .logicLit p e =>
    let e := (Choice.takeFirst? e (choiceOrder ctx)).getD e
    let r ← operand { ctx with canFail := true, inTaking := true } e none
    if !(r.e.mayFail ctx.sigProg) && (← ctx.failabilityKnown) then eerr p "logic{…} needs an expression that can fail"
    return ⟨Expr.logicE (← inferable r), .logic⟩
  | _ => eerr se.pos "internal: expression routed to the wrong elaboration stage"

end OpenVerse.Front
