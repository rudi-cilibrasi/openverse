# followup-corners (#724): A map literal whose keys are of two <unique>
# classes, cat and dog, whose only common class, animal, is not <unique> (so
# not comparable): admitted, keyed by comparable?
# OpenVerse (Lean and C agreeing): refused, expected cat, found dog (the
# class above both is no key type, and OpenVerse does not go on to
# comparable).
# If Epic refuses it, OpenVerse agrees on the verdict. If it admits it and
# prints length 2 cat 1 dog 2, the keys join to comparable past a class that
# is not: OpenVerse would do so.
# Not yet compiled or run by UEFN.
animal := class:
    Legs:int = 4

cat := class<unique>(animal){}
dog := class<unique>(animal){}

Main():void =
    C := cat{}
    D := dog{}
    M := map{C => 1, D => 2}
    A := if (V := M[C]) then V else -1
    B := if (V := M[D]) then V else -1
    Print("OVPROBE length {M.Length} cat {A} dog {B}")
