/- Initializer admission, separate from heap permissions and execution fuel. -/
import OpenVerse.Front.Syntax
import OpenVerse.Front.FinalSuper
import OpenVerse.Core.Semantics
import Std.Data.HashSet

namespace OpenVerse.Front.InitializerConvergence
open OpenVerse

/-- Retain ordinary source-call provenance through extraction and adapters.
    This private marker makes no assertion about the function's implementation. -/
def sourceCallMarker : String := "$initializerOrdinaryCall"

def markFunction : STop → STop
  | .fn p n ps ts specs ret body =>
    .fn p n ps ts (sourceCallMarker :: specs) ret body
  | t => t

def markSource : STop → STop
  | .classDef p n nsp ts specs parents iface fields methods =>
    .classDef p n nsp ts specs parents iface fields (methods.map fun

      | m@(.fn _ "$block" ..) => m
      | m => markFunction m)
  | t => markFunction t

/-- An overapproximation of falling through with an ordinary value. A false
    result proves that a loop body cannot reach its next iteration. -/
def mayNormal : Expr → Bool
  | .assign _ e | .print e => mayNormal e
  | .seq a b => mayNormal a && mayNormal b
  | .ite _ a b => mayNormal a || mayNormal b
  | .brk | .ret _ | .prim .fail [] => false
  | _ => true

theorem mayNormal_of_eval {P : Prog} {s s' : St} {e : Expr} {v : Value}
    (h : Eval P s e (.ok v) s') : mayNormal e = true := by
  cases e with
  | assign i e =>
    cases h with
    | assign_ok he _ => simpa [mayNormal] using mayNormal_of_eval he
    | assign_stop _ hn => simp [Res.isOk] at hn
  | seq a b =>
    cases h with
    | seq_ok ha hb => simp [mayNormal, mayNormal_of_eval ha, mayNormal_of_eval hb]
    | seq_stop _ hn => simp [Res.isOk] at hn
  | ite c a b =>
    cases h with
    | ite_ok _ ha => simp [mayNormal, mayNormal_of_eval ha]
    | ite_fail _ hb => simp [mayNormal, mayNormal_of_eval hb]
    | ite_stop _ hn _ => simp [Res.isOk] at hn
  | print e =>
    cases h with
    | print_ok he _ => simpa [mayNormal] using mayNormal_of_eval he
    | print_stop _ hn => simp [Res.isOk] at hn
  | brk => cases h
  | ret e => cases h <;> simp_all [Res.isOk]
  | prim op es =>
    cases op <;> try rfl
    cases es with
    | cons _ _ => rfl
    | nil =>
      generalize hr : Res.ok v = result at h
      cases h with
      | prim_ok hs => cases hs; cases hr
      | prim_stop hs => cases hs
  | _ => rfl
termination_by sizeOf e

/-- A body is admitted only after its helpers are materialized. Ordinary source
    functions retain their non-convergent contract even when they return a
    literal. Compiler implementation calls are inspected, with memoization and
    cycle rejection. Construction blocks are the explicit Book exception;
    finite compiler-owned intrinsic expansions retain their trusted contract.
    Finite `for` and failure/multiple values do not imply divergence. -/
partial def checkExpr (fns : Array Fn) (ordinary construction : List String)
    (visiting : List Nat) (e : Expr) : StateT (Std.HashSet Nat) (Except String) Unit := do
  let recur := checkExpr fns ordinary construction visiting
  match e with
  | .lit _ | .local _ | .brk => pure ()
  | .assign _ e | .ret e | .print e => recur e
  | .seq a b => recur a; recur b
  | .prim _ es | .heap _ es => es.forM recur
  | .ite c a b => recur c; recur a; recur b
  | .forE _ source filter body => recur source; recur filter; recur body
  | .loop body =>
    if mayNormal body then throw "a loop has no checked convergence contract"
    recur body
  | .call idx args =>
    args.forM recur
    let some fn := fns[idx]? | throw "an initializer calls an unavailable helper"
    if ordinary.contains fn.name then
      throw s!"ordinary function '{(FinalSuper.calledBy? fn.name).getD fn.name}' has no checked convergence contract"
    if construction.contains fn.name then return
    if visiting.contains idx then
      throw s!"recursive helper '{fn.name}' has no checked convergence contract"
    if (← get).contains idx then return
    checkExpr fns ordinary construction (idx :: visiting) fn.body
    modify (·.insert idx)

end OpenVerse.Front.InitializerConvergence
