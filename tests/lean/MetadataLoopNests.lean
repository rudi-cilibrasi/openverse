/- Loops inside loops in the metadata flow check (#761). A loop that an
   enclosing loop reaches again resumes from its last stable head joined with
   the new entry, in a body with or without private cells, so a nest of n
   loops costs a number of passes quadratic in n, where it cost 2^n. These
   Core models are the flows a resumed head must not lose, in nests of up to
   twenty-four loops (sixteen million passes before): metadata that needs the
   back edge of every level to reach an executable use, outward from the
   innermost body and inward from the entry, through `loop` and `forE`, in a
   body with a cleanup and in one without. Each has the control whose chain
   lacks one link, which must stay admitted: a resumed head may not be larger
   than the fixed point either.
   These are compiler API models with valid Core programs. -/
import OpenVerse

open OpenVerse OpenVerse.Front
namespace MetadataLoopNests

private def callable : VTy := .ref [1] []
private def execute (value : Expr) : Expr := .call 0 [value]
private def void (e : Expr) : Expr := .seq e (.lit .void)

/-- `Root(first, real, count)` with a nest of `depth` loops. Slot `3 + k` is
    the carrier `a k` of level `k` (level 0 is the outermost loop, `a depth`
    belongs to the innermost body), slot `4 + depth + k` the item of level
    `k` when it is a `forE`. Every other level is a `forE` when `fors`.

    - `outward`: the innermost body takes `first`, each level copies the
      carrier of the level inside it *before* that level's loop, and the
      outermost body executes `a 0` first of all. The value moves out one
      level per pass of that level, so it arrives only over every back edge.
    - `inward`: `a 0` is `first` before the nest, each level copies its
      carrier to the next *after* the loop inside it, and the innermost body
      executes `a depth`. The value moves in one level per pass, through the
      entry of a loop that has already reached its fixed point once.
    - `broken`: a link in the middle of the chain copies `real` instead. -/
private def root (shape : String) (broken : Bool) (depth : Nat) (fors cleanup : Bool) : Fn :=
  let a (k : Nat) : Nat := 3 + k
  let item (k : Nat) : Nat := 4 + depth + k
  let leave : Expr := .ite (.prim .eq [.local 2, .lit (.int 0)]) .brk (.lit .void)
  let wrap (k : Nat) (body : Expr) : Expr :=
    if fors && k % 2 == 1 then
      void (.forE (item k) (.prim .mkArr [.local 1, .local 1]) (.prim .eq [.local 2, .lit (.int 1)]) body)
    else .loop (.seq leave body)
  let cut := if shape == "outward" then depth / 2 else (depth + 1) / 2
  let link (k : Nat) (source : Nat) : Expr :=
    void (.assign (a k) (if broken && k == cut then .local 1 else .local source))
  -- (`foldr` puts level 0 outermost)
  let nest : Expr := match shape with
    | "outward" =>
      (List.range depth).foldr (fun k inner =>
        wrap k (.seq (if k == 0 then void (execute (.local (a 0))) else .lit .void)
          (.seq (link k (a (k + 1))) inner))) (void (.assign (a depth) (.local 0)))
    | _ =>
      (List.range depth).foldr (fun k inner =>
        wrap k (.seq inner (link (k + 1) (a k)))) (void (execute (.local (a depth))))
  let start : Expr := if shape == "outward" then .lit .void else void (.assign (a 0) (.local 0))
  let code : Expr := .seq start (.seq nest (.lit .void))
  -- (a cleanup's marker, as a `defer` lowers: the body then takes the
  -- check's discovery and validating passes instead of the plain one)
  let code := if cleanup then .seq (.ite (.prim .fail []) (.lit .void) (.lit .void)) code else code
  let locals := 2 * depth + 1
  let body := (List.range locals).foldr (fun i rest => Expr.seq (.assign (3 + i) (.local 1)) rest) code
  { name := "Root", arity := 3, nslots := 3 + locals, decides := true, writes := true, body }

private def classify (shape : String) (broken : Bool) (depth : Nat) (fors cleanup metadata : Bool) : IO Bool := do
  let sink : Fn := { name := "Execute", arity := 1, nslots := 1, decides := false, body := .lit .void }
  let caller := root shape broken depth fors cleanup
  let closed : Fn := { name := "ClosedRoot", arity := 0, nslots := 0, decides := false, body := .lit .void }
  let fns := #[sink, caller, closed]
  let sigs : Sigs := {
    fns := [([callable], .void), ([callable, callable, .int], .void), ([], .void)]
    classes := [[.var 0], []], pins := [[none], []] }
  let slots := [[callable], [callable, callable, .int] ++ List.replicate (caller.nslots - 3) callable, []]
  let prog : Prog := { fns := fns.toList, main := 2 }
  unless prog.check && prog.checkControl && prog.checkTypes sigs slots && checkPrelude prog sigs do
    throw <| IO.userError s!"invalid Core model: {shape} depth {depth}"
  let infos : Array MetadataFlow.Info := fns.mapIdx fun index fn => {
    body := some fn.body
    inputs := if index == 1 && metadata then [0] else []
    required := if index == 0 then [0] else [] }
  let results := sigs.fns.toArray.map fun (_, result) => MetadataValues.objectFree result
  match MetadataFlow.check fns infos #[[], []] false results with
  | .ok _ => pure true
  | .error _ => pure false

def main : IO Unit := do
  let mut count := 0
  let mut bad := 0
  for shape in ["outward", "inward"] do
    for depth in [1, 2, 3, 5, 9, 24] do
      for fors in [false, true] do
        for cleanup in [false, true] do
          for broken in [false, true] do
            for metadata in [false, true] do
              let admitted ← classify shape broken depth fors cleanup metadata
              count := count + 1
              -- Metadata reaches Execute exactly when Root's first input is
              -- metadata and every link of the chain is there.
              if admitted == (metadata && !broken) then
                bad := bad + 1
                IO.println s!"mismatch: {shape} depth={depth} fors={fors} cleanup={cleanup} broken={broken} metadata={metadata} admitted={admitted}"
  IO.println s!"{count} loop-nest policy classifications; {bad} mismatches"
  if bad > 0 then throw <| IO.userError "loop nest policy mismatch"
end MetadataLoopNests

def main : IO Unit := MetadataLoopNests.main
