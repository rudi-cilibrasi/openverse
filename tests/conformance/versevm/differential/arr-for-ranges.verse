# for over ranges: ordinary, of one element, empty (bounds reversed),
# negative, and the result array of a for whose filter rejects everything.
# Tests LANGUAGE.md, Control: "X := a..b"; a range a..b with a > b is empty.
# OpenVerse prints (Lean and C agree):
#   [1,4,9,16] [3] [] [-2,-1,0,1] [] 0 0
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")

Main():void =
    A := for (I := 1..4) { I * I }
    B := for (I := 3..3) { I }
    C := for (I := 3..1) { I }
    D := for (I := -2..1) { I }
    E := for (I := 1..5, I > 9) { I }
    Print("OVPROBE [{Show(A)}] [{Show(B)}] [{Show(C)}] [{Show(D)}] [{Show(E)}] {C.Length} {E.Length}")
