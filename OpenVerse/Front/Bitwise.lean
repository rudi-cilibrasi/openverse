/-
  OpenVerse front end — the bitwise functions, written in Verse.

  The Book of Verse (ch. 4, "Bitwise Operations" and "Bit Shift
  Operations"; its API reference) defines `BitAnd`, `BitOr`, `BitXor` and
  `BitNot` on "two's-complement bit patterns of unlimited width. Negative
  values behave as though sign-extended forever to the left", and
  `BitShiftLeft[X, N]`, `BitShiftRight[X, N]`, which fail on a negative
  count and are arithmetic: a right shift rounds toward minus infinity.
  openverse's ints are the Blueprint VM's, 64 bits with a runtime error
  outside (`Math/Bitwise.versetest`'s `bp_vm_only` cases): a result is the
  unbounded one when it is in range, and an overflow is Verse Core's
  overflow error, as for any other int operation.

  They are written with Verse Core's existing operations, so Verse Core,
  its proofs, the binary format and the C runtime are unchanged. `BitNot(X)`
  is `-1 - X` (which cannot overflow), inline. The others are helpers here,
  which the elaborator adds to a program that names one of them
  (`bitwiseMarker`, from the parser):

  - `bitAnd`, `bitOr`, `bitXor` take the operands' two's complement bits
    from the lowest up, by halving with `Floor(X / 2)` (which rounds toward
    minus infinity, so a negative number's bits are its two's complement),
    and stop once both operands are 0 or -1: every bit from there up is
    its sign. The result's bits below are summed; the bits from there up
    are all the operation of the two signs, which, sign-extended, weigh
    `-2^i` together (`N`, the negated weight, from -1 down to at most
    `-2^63`, which is in range). Every number they compute is in range.
    A call takes at most 63 rounds, and as many as the operands' highest
    differing bit.
  - `bitShiftLeft` doubles `X` `N` times, or until it is 0; a doubling out
    of range is the overflow error, which a result out of range always
    reaches (the magnitudes only grow), and no earlier.
  - `bitShiftRight` halves `X` (rounding toward minus infinity) `N` times,
    or until it is 0 or -1, which halving keeps.
-/
import OpenVerse.Front.Parser

namespace OpenVerse.Front

/-- The helpers' names, and their parameters' and locals' (which must not
    collide with a program's definitions): each becomes `$name`, which no
    program can write. -/
def bitwiseNames : List String :=
  ["bitAnd", "bitOr", "bitXor", "bitShiftLeft", "bitShiftRight",
   "A", "B", "R", "N", "X", "Y", "I", "H", "HA", "HB"]

def bitwisePrelude : String := "
bitAnd(X:int, Y:int)<computes>:int =
    var A:int = X
    var B:int = Y
    var R:int = 0
    var N:int = -1
    loop:
        if (-1 <= A <= 0, -1 <= B <= 0) then break
        if (HA := Floor(A / 2), HB := Floor(B / 2)):
            if (A - 2 * HA = 1, B - 2 * HB = 1) then set R -= N
            set A = HA
            set B = HB
            set N *= 2
    if (A = -1, B = -1) then R + N else R

bitOr(X:int, Y:int)<computes>:int =
    var A:int = X
    var B:int = Y
    var R:int = 0
    var N:int = -1
    loop:
        if (-1 <= A <= 0, -1 <= B <= 0) then break
        if (HA := Floor(A / 2), HB := Floor(B / 2)):
            if (A - 2 * HA = 1 or B - 2 * HB = 1) then set R -= N
            set A = HA
            set B = HB
            set N *= 2
    if (A = -1 or B = -1) then R + N else R

bitXor(X:int, Y:int)<computes>:int =
    var A:int = X
    var B:int = Y
    var R:int = 0
    var N:int = -1
    loop:
        if (-1 <= A <= 0, -1 <= B <= 0) then break
        if (HA := Floor(A / 2), HB := Floor(B / 2)):
            if (A - 2 * HA <> B - 2 * HB) then set R -= N
            set A = HA
            set B = HB
            set N *= 2
    if (A <> B) then R + N else R

bitShiftLeft(X:int, N:int)<computes><decides>:int =
    N >= 0
    var R:int = X
    var I:int = 0
    loop:
        if (R = 0 or I >= N) then break
        set R *= 2
        set I += 1
    R

bitShiftRight(X:int, N:int)<computes><decides>:int =
    N >= 0
    var R:int = X
    var I:int = 0
    loop:
        if (I >= N or -1 <= R <= 0) then break
        if (H := Floor(R / 2)) then set R = H
        set I += 1
    R
"

/-- Whether an expression names a bitwise function that needs a helper (an
    entry expression, `openverse run FILE do EXPR`). -/
partial def mentionsBitwise : SExpr → Bool
  | .ident _ n => n != "BitNot" && bitwiseFunctions.contains n
  | e => e.children.any mentionsBitwise

/-- The helpers, parsed (their names renamed). -/
def bitwiseTops : Except String (List STop) := parsePrelude bitwisePrelude bitwiseNames

end OpenVerse.Front
