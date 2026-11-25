/-
  OpenVerse front end — `GetRandomInt`, written in Verse (#724).

  Epic's `GetRandomInt(Low:int, High:int)<transacts>:int` (the Book's
  Runtime API reference, module `/Verse.org/Random`) is "a uniformly
  distributed int in [Low, High], both ends included, with the bounds
  accepted in either order", drawn from a hardware entropy seed: "There is
  no seed parameter and no way to replay a sequence". openverse is
  deterministic, so its `GetRandomInt` is a documented generator with a
  fixed seed instead: every run of a program draws the same numbers, in the
  reference interpreter and in the C runtime alike.

  The generator is Knuth's 64-bit linear congruential generator (MMIX's
  constants), `S' = (6364136223846793005·S + 1442695040888963407) mod 2^64`,
  from `S = 0`; a draw is the high 32 bits of the new state. A call draws
  until it has at least 32 bits more than its range, `|High - Low| + 1`,
  needs (one draw for a range below 2^32), takes the draws as one number
  `R`, the first the most significant, and gives `Min(Low, High) + R mod
  range`: every value of the range, with a bias below 2^-32.

  The state is the one `var` field of the prototype of a hidden class
  (`randomCell`, as `ModuleVars` holds the module-scoped variables), so
  Verse Core, its proofs, the binary format and the C runtime are unchanged.
  It is written as any field is: a failure context that fails undoes its
  draws (Epic's draw "is deliberately taken outside the enclosing
  transaction"; no program can tell the difference from the numbers alone).
-/
import OpenVerse.Front.Parser

namespace OpenVerse.Front

/-- The helper's names (each becomes `$name`, which no program can write). -/
def randomNames : List String :=
  ["randomState", "randomCell", "randomInt", "S", "C", "Low", "High", "Lo", "Span", "R", "Bound", "Q", "M"]

/-- The class whose prototype holds the generator's state, and the name its
    helper reads the prototype by (`ExpressionInitial`). -/
def randomStateClass : String := "$randomState"
def randomCellName : String := "$randomCell"

def randomPrelude : String := "
randomState := class:
    var S:int = 0

randomInt(Low:int, High:int)<transacts>:int =
    C := randomCell
    Lo := if (Low <= High) then Low else High
    Span := (if (Low <= High) then High - Low else Low - High) + 1
    var R:int = 0
    var Bound:int = 1
    loop:
        if (Bound >= Span * 4294967296) then break
        if (M := Mod[C.S * 6364136223846793005 + 1442695040888963407, 4294967296 * 4294967296]):
            set C.S = M
        if (Q := Quotient[C.S, 4294967296]):
            set R = R * 4294967296 + Q
        set Bound *= 4294967296
    if (M := Mod[R, Span]) then Lo + M else Lo
"

/-- Whether an expression names `GetRandomInt` (an entry expression,
    `openverse run FILE do EXPR`). -/
partial def mentionsRandom : SExpr → Bool
  | .ident _ n => n == "GetRandomInt"
  | e => e.children.any mentionsRandom

/-- The helper, parsed (its names renamed). -/
def randomTops : Except String (List STop) := parsePrelude randomPrelude randomNames

end OpenVerse.Front
