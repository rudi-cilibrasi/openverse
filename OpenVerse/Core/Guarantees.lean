/-
  OpenVerse — what every program accepted by the front end is guaranteed.

  The front end (`OpenVerse.Front.compile`) accepts a program only if it
  passes `Prog.check` and, with the signatures and slot types it computed,
  `Prog.checkTypes`. Both checks are proved sound, so the theorems about
  Verse Core apply to every accepted program:

  * it has at most one outcome and one output (`Runs.det`);
  * it never raises a slot or call error (`Runs.scoped_ok`);
  * it never raises a type error, it ends with a well-typed heap, and a
    successful `Main` returns a value of its declared type in that heap
    (`Runs.typed`);
  * it never fails unless `Main` is `<decides>` (`Runs.no_fail`).

  * it never raises a control error: `break` stays inside its loop
    (`Runs.no_control`).

  The only runtime errors left are integer overflow and `Err()`.
-/
import OpenVerse.Core.Check
import OpenVerse.Core.TypeCheck
import OpenVerse.Core.Control

namespace OpenVerse

theorem Prog.accepted {P : Prog} {S : Sigs} {Γs : List (List VTy)} {τ : VTy}
    (hc : P.check = true) (ht : P.checkTypes S Γs = true) (hctl : P.checkControl = true)
    (hm : S.fns[P.main]? = some ([], τ)) {r : Res} {out : List Nat} (hr : Runs P r out) :
    r.scopeErr = false ∧ r ≠ .err .type ∧ r ≠ .err .control ∧
    (∃ fr heap, Eval P Prog.initSt (.call P.main []) r ⟨fr, ⟨out, heap⟩⟩ ∧
      ∃ Ξ, HeapOK S Ξ heap ∧ ∀ v, r = .ok v → hasTy Ξ v τ = true) ∧
    (∀ fn, P.fns[P.main]? = some fn → fn.decides = false → r ≠ .fail) ∧
    (∀ r' out', Runs P r' out' → r' = r ∧ out' = out) := by
  obtain ⟨hs, hf⟩ := Prog.check_ok hc hr
  obtain ⟨hty, hv⟩ := Runs.typed (Prog.checkTypes_sound ht) hm hr
  exact ⟨hs, hty, Runs.no_control hctl hr, hv, hf, fun r' out' h' => Runs.det h' hr⟩

/-- **What a function without `writes` guarantees** (#35). In a program
    that passes `Prog.check`, a call of a function marked as not writing
    (`<computes>`, `<reads>`, `<allocates>`), with arguments that do not
    write, leaves every existing object, at its address, with its fields. -/
theorem Prog.accepted_no_writes {P : Prog} (hc : P.check = true) {s f es r s' fn}
    (hf : P.fns[f]? = some fn) (hw : fn.writes = false) (hes : Expr.writesHeapList P es = false)
    (h : Eval P s (.call f es) r s') : s.g.keeps s'.g :=
  call_no_writes (Prog.check_writeSound hc) hf hw hes h

end OpenVerse
