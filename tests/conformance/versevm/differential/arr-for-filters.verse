# for over arrays with filters, indices, bindings and two generators: the
# iteration order and what the result array holds.
# Tests LANGUAGE.md, Control: "for with X : array, I -> X : array, X :=
# a..b, filters, bindings, several generators (cartesian product)"; ch. 7:
# nested generators give the product, leftmost outermost.
# OpenVerse prints (Lean and C agree):
#   a 4,3 11,23,32 9,4 | b 11,12,13,22,23,33 17,28
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")

Main():void =
    A:[]int = array{4, 1, 3, 2}
    Big := for (X : A, X > 2) { X }
    Pos := for (I -> X : A, I > 0, X < 4) { I * 10 + X }
    Sq := for (X : A, Y := X * X, Y > 3, Y < 15) { Y }
    Print("OVPROBE a {Show(Big)} {Show(Pos)} {Show(Sq)}")
    Pairs := for (X := 1..3, Y := X..3) { X * 10 + Y }
    Cross := for (X : array{1, 2}, Y : array{7, 8}, X + Y <> 9) { X * 10 + Y }
    Print("OVPROBE b {Show(Pairs)} {Show(Cross)}")
