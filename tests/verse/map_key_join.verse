# A map literal's key type, with none expected, is the join of its keys'
# types (#724): "Map literals should infer common key and value types that
# are joins of the key and value types of each pair" (the Book's tests,
# Map.versetest:143). Keys of sibling classes, of a class and one below or
# above it, in any order, make a map keyed by the <unique> class above them
# (Epic's compiler and Verse VM, UEFN 43.12,
# followup-refused/map-literal-sibling-keys: looked up). A key is looked up
# by identity, whatever its class.
base := class<unique>{}
child_a := class(base){}
child_b := class(base){}
grand := class(child_a){}
small := type{_X:int where 0 <= _X, _X < 10}

Count(M:[base]int):int = M.Length

Main():void =
    A := child_a{}
    B := child_b{}
    S := base{}
    G := grand{}
    # siblings, the class above them, one below; a key given twice
    M := map{A => 1, B => 2, S => 3, G => 4, A => 5}
    if (M[A] = 5, M[B] = 2, M[S] = 3, M[G] = 4):
        Print("looked up {M.Length} {Count(M)}")
    C := child_b{}
    if (not M[C]). Print("another object is no key")
    K:base = B
    if (X := M[K]). Print("by its base {X}")
    for (Key -> V : M). Print("{V}")
    # the class below first
    M2 := map{G => 1, A => 2}
    if (M2[A] = 2, M2[G] = 1). Print("m2 {M2.Length}")
    # options and tuples of them
    M3 := map{option{A} => 1, option{B} => 2, false => 3}
    if (M3[option{B}] = 2, M3[false] = 3). Print("m3 {M3.Length}")
    M4 := map{(A, 1) => "a", (B, 1) => "b"}
    if (V := M4[(B, 1)]). Print("m4 {V}")
    # a refinement and its base, at the base
    R:small = 3
    M5 := map{R => "r", 70 => "int"}
    if (V := M5[70], W := M5[3]). Print("m5 {V} {W}")
