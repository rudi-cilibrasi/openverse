# followup-corners (#724): Control for map-unique-sibling-keys: the same
# with animal <unique>, so the keys join to a comparable class.
# OpenVerse (Lean and C agreeing): ran, length 2 cat 1 dog 2.
# If Epic prints the same, a refusal of map-unique-sibling-keys is about the
# class that is not <unique>. If it refuses this, sibling keys do not join
# at all in a map literal with no type written: OpenVerse would refuse it.
# Not yet compiled or run by UEFN.
animal := class<unique>:
    Legs:int = 4

cat := class(animal){}
dog := class(animal){}

Main():void =
    C := cat{}
    D := dog{}
    M := map{C => 1, D => 2}
    A := if (V := M[C]) then V else -1
    B := if (V := M[D]) then V else -1
    Print("OVPROBE length {M.Length} cat {A} dog {B}")
