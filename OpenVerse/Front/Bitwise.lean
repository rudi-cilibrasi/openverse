/-
  OpenVerse front end — the bitwise functions, written in Verse.

  The Book of Verse (ch. 4, "Bitwise Operations" and "Bit Shift
  Operations"; its API reference) defines `BitAnd`, `BitOr`, `BitXor` and
  `BitNot` on "two's-complement bit patterns of unlimited width. Negative
  values behave as though sign-extended forever to the left", and
  `BitShiftLeft[X, N]`, `BitShiftRight[X, N]`, which fail on a negative
  count and are arithmetic: a right shift rounds toward minus infinity.
  openverse's ints are the Verse VM's (#724), of up to 2^20 bits
  (`Math/Bitwise.versetest`'s `verse_vm_only` cases, "MaxLengthBits"): a
  longer result is Verse Core's overflow error, as for any other int
  operation.

  They are written with Verse Core's existing operations, so Verse Core,
  its proofs, the binary format and the C runtime are unchanged. `BitNot(X)`
  is `-1 - X` (which cannot overflow), inline. The others are helpers here,
  which the elaborator adds to a program that names one of them
  (`bitwiseMarker`, from the parser):

  - `bitAnd`, `bitOr`, `bitXor` take the operands' two's complement bits
    from the lowest up, by halving with `Floor(X / 2)` (which rounds toward
    minus infinity, so a negative number's bits are its two's complement),
    and stop once both operands are 0 or -1: every bit from there up is
    its sign. The result's bits below are summed (`N`, the negated weight
    of the bit taken, -1, -2, -4, …); the bits from there up are all the
    operation of the two signs, which, sign-extended, weigh `2N` together,
    added as `N + N`, so no number they compute is longer than an operand.
    A call takes as many rounds as the operands' highest differing bit.
  - `bitPow2(N)` is 2^N for N ≥ 0, by squaring: 2^(2^k) is computed only
    while bits of `N` remain above k, so no number it computes is larger
    than 2^N, and 2^N past the length limit is the overflow error.
  - `bitShiftLeft[X, N]` is `X · 2^N` (0 when `X` is 0, whatever `N`);
    `bitShiftRight[X, N]` is `Floor(X / 2^N)`, 0 or -1 once `N` reaches
    the length limit (no int has as many bits).
-/
import OpenVerse.Front.Parser

namespace OpenVerse.Front

/-- The helpers' names, and their parameters' and locals' (which must not
    collide with a program's definitions): each becomes `$name`, which no
    program can write. -/
def bitwiseNames : List String :=
  ["bitAnd", "bitOr", "bitXor", "bitPow2", "bitShiftLeft", "bitShiftRight",
   "A", "B", "R", "N", "X", "Y", "HA", "HB", "E", "Q"]

def bitwisePrelude : String := "
bitAnd(X:int, Y:int)<computes>:int =
    var A:int = X
    var B:int = Y
    var R:int = 0
    var N:int = 0
    loop:
        if (-1 <= A <= 0, -1 <= B <= 0) then break
        set N = if (N = 0) then -1 else 2 * N
        if (HA := Floor(A / 2), HB := Floor(B / 2)):
            if (A - 2 * HA = 1, B - 2 * HB = 1) then set R -= N
            set A = HA
            set B = HB
    if (A = -1, B = -1) then (if (N = 0) then -1 else R + N + N) else R

bitOr(X:int, Y:int)<computes>:int =
    var A:int = X
    var B:int = Y
    var R:int = 0
    var N:int = 0
    loop:
        if (-1 <= A <= 0, -1 <= B <= 0) then break
        set N = if (N = 0) then -1 else 2 * N
        if (HA := Floor(A / 2), HB := Floor(B / 2)):
            if (A - 2 * HA = 1 or B - 2 * HB = 1) then set R -= N
            set A = HA
            set B = HB
    if (A = -1 or B = -1) then (if (N = 0) then -1 else R + N + N) else R

bitXor(X:int, Y:int)<computes>:int =
    var A:int = X
    var B:int = Y
    var R:int = 0
    var N:int = 0
    loop:
        if (-1 <= A <= 0, -1 <= B <= 0) then break
        set N = if (N = 0) then -1 else 2 * N
        if (HA := Floor(A / 2), HB := Floor(B / 2)):
            if (A - 2 * HA <> B - 2 * HB) then set R -= N
            set A = HA
            set B = HB
    if (A <> B) then (if (N = 0) then -1 else R + N + N) else R

bitPow2(N:int)<computes>:int =
    var R:int = 1
    var B:int = 2
    var E:int = N
    loop:
        if (E <= 0) then break
        if (Mod[E, 2] = 1) then set R *= B
        if (Q := Quotient[E, 2]) then set E = Q
        if (E > 0) then set B *= B
    R

bitShiftLeft(X:int, N:int)<computes><decides>:int =
    N >= 0
    if (X = 0) then 0 else X * bitPow2(N)

bitShiftRight(X:int, N:int)<computes><decides>:int =
    N >= 0
    # (an int has at most 2^20 bits, IntBits.max)
    if (N >= 1048576) then (if (X < 0) then -1 else 0)
    else if (Q := Floor(X / bitPow2(N))) then Q else 0
"

/-- Whether an expression names a bitwise function that needs a helper (an
    entry expression, `openverse run FILE do EXPR`). -/
partial def mentionsBitwise : SExpr → Bool
  | .ident _ n => n != "BitNot" && bitwiseFunctions.contains n
  | e => e.children.any mentionsBitwise

set_option compiler.extract_closed false in
/-- The helpers, parsed (their names renamed). -/
def bitwiseTops : Thunk (Except String (List STop)) :=
  Thunk.mk fun _ => parsePrelude bitwisePrelude bitwiseNames

end OpenVerse.Front
