# The bitwise functions are of one signature each: named as values they are
# function values (BitShiftLeft and BitShiftRight <decides>); and a program
# may define its own of their names, which its calls then mean.
Fold(F(:int, :int):int, Start:int, Xs:[]int):int =
    var Acc:int = Start
    for (X : Xs) do set Acc = F(Acc, X)
    Acc
Shifted(F(:int, :int)<decides>:int, X:int, N:int):int = if (R := F[X, N]) then R else -1
BitXor(X:int, Y:int):int = X + Y
Main():void =
    Print("{Fold(BitOr, 0, array{1, 4, 16})} {Fold(BitAnd, -1, array{7, 13})} {BitXor(2, 3)}")
    G := BitNot
    Print("{G(5)} {Shifted(BitShiftLeft, 3, 2)} {Shifted(BitShiftRight, -9, 1)} {Shifted(BitShiftLeft, 3, -2)}")
