# regression test for the C runtime's field roots (#50 review, r1): Lean and C must agree
box := class:
    var A:[]int = array{}

FailAfterPut(B:box)<decides>:void =
    set B.A = array{99, 99, 99}
    1 > 2

G(B:box):int =
    set B.A = array{1, 2, 3}
    if (FailAfterPut[B]) {}
    0

H(B:box):int =
    G(B)
    0

Main():void =
    B := box{}
    H(B)
    X := array{7, 8, 9, 10, 11}
    Print("{X.Length} {B.A.Length}")
    for (V : B.A) { Print("{V}") }
