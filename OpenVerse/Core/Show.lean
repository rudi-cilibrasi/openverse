/-
  A compact, readable rendering of Verse Core expressions and values, in
  time linear in their size: for `openverse core` and the
  `OPENVERSE_DEBUG` dump, where `repr` (Lean's pretty printer) takes
  minutes on the bodies of large programs.

  One statement of a sequence per line, indented by nesting; `$i` is slot
  `i`, `#f` function `f`, `@a` heap address `a`; an array of characters is
  shown as a string.
-/
import OpenVerse.Core.Syntax

namespace OpenVerse

/-- A character as Verse source writes it. -/
def showChar (c : Nat) : String :=
  if c == 10 then "\\n" else if c == 9 then "\\t" else if c == 34 then "\\\""
  else if c == 92 then "\\\\" else if c ≥ 32 && c < 127 then (Char.ofNat c).toString
  else s!"\\u\{{c}}"

/-- A value, compactly. -/
partial def Value.compact : Value → String
  | .int i => toString i
  | .logic b => if b then "true" else "false"
  | .char c => "'" ++ showChar c ++ "'"
  | .float b => s!"float({Float.ofBits b})"
  | .arr a =>
    if !a.isEmpty && a.all (fun | .char _ => true | _ => false) then
      "\"" ++ String.join (a.toList.map fun | .char c => showChar c | _ => "") ++ "\""
    else "[" ++ ", ".intercalate (a.toList.map Value.compact) ++ "]"
  | .tup vs => "(" ++ ", ".intercalate (vs.map Value.compact) ++ ")"
  | .none => "none"
  | .some v => s!"some({v.compact})"
  | .ref a => s!"@{a}"

/-- A primitive's name. -/
def Prim.name : Prim → String
  | .tupGet k => s!"tupGet{k}"
  | p => match (repr p).pretty.splitOn "." with
    | [] => "?"
    | xs => xs.getLast!

namespace Expr

/-- A heap operation applied to its operands. -/
def heapShow (op : HeapOp) (args : List String) : String :=
  let a := ", ".intercalate args
  match op with
  | .new t => s!"new{t}({a})"
  | .get k => s!"get{k}({a})"
  | .set k => s!"set{k}({a})"
  | .tag => s!"tag({a})"
  | .isTag us => s!"isTag{us}({a})"

mutual
/-- An expression on one line, when it has no statements inside. -/
partial def inline : Expr → Option String
  | .lit v => some v.compact
  | .local i => some s!"${i}"
  | .assign i e => (inline e).map (s!"${i} := " ++ ·)
  | .prim op es => (es.mapM inline).map fun xs => s!"{Prim.name op}(" ++ ", ".intercalate xs ++ ")"
  | .call f es => (es.mapM inline).map fun xs => s!"#{f}(" ++ ", ".intercalate xs ++ ")"
  | .heap op es => (es.mapM inline).map (heapShow op ·)
  | .brk => some "break"
  | .ret e => (inline e).map ("return " ++ ·)
  | .print e => (inline e).map ("print " ++ ·)
  | .ite c t e => do
    let (c, t, e) := (← inline c, ← inline t, ← inline e)
    if c.length + t.length + e.length > 100 then none else some s!"(if {c} then {t} else {e})"
  | _ => none

/-- An expression as lines, at indentation `ind`, into `out`. -/
partial def lines (ind : String) (e : Expr) (out : Array String) : Array String :=
  match inline e with
  | some s => out.push (ind ++ s)
  | none =>
    let ind' := ind ++ "  "
    match e with
    | .seq a b => lines ind b (lines ind a out)
    | .assign i e => lines ind' e (out.push s!"{ind}${i} :=")
    | .ite c t f =>
      let out := match inline c with
        | some s => out.push s!"{ind}if {s} then"
        | none => (lines ind' c (out.push s!"{ind}if")).push s!"{ind}then"
      let out := lines ind' t out
      lines ind' f (out.push s!"{ind}else")
    | .forE i a f b =>
      let out := lines ind' a (out.push s!"{ind}for ${i} in")
      let out := lines ind' f (out.push s!"{ind}where")
      lines ind' b (out.push s!"{ind}do")
    | .loop b => lines ind' b (out.push s!"{ind}loop")
    | .ret e => lines ind' e (out.push s!"{ind}return")
    | .print e => lines ind' e (out.push s!"{ind}print")
    | .prim op es => es.foldl (fun o e => lines ind' e o) (out.push s!"{ind}{Prim.name op}(…)")
    | .call f es => es.foldl (fun o e => lines ind' e o) (out.push s!"{ind}#{f}(…)")
    | .heap op es => es.foldl (fun o e => lines ind' e o) (out.push s!"{ind}{heapShow op ["…"]}")
    | e => out.push (ind ++ ((inline e).getD "?"))
end

/-- An expression as text, one statement per line, each line starting
    with `ind`; at most `cap` lines (then an ellipsis). -/
def compact (e : Expr) (ind : String := "") (cap : Nat := 4000) : String :=
  let ls := lines ind e #[]
  let ls := if ls.size > cap then (ls.extract 0 cap).push s!"{ind}… ({ls.size - cap} more lines)" else ls
  "\n".intercalate ls.toList

end Expr
end OpenVerse
