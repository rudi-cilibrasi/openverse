# An argument, or a case's value, may be a sequence: `F(1; 2)` evaluates 1,
# then passes 2 (Book of Verse ch. 1, "Semicolons vs Commas": `Process(
# LogEvent("called"); 42)`; its tests: `F0(99;100,20)`, `case(Bar; Baz)`).
F(A:int, B:int):int = A * 10 + B
G(I:int)<decides>:int = I + 1
Main():void =
    var Count:int = 0
    R := F(set Count = 5; 2, 3)
    C := case(set Count += 1; 3):
        3 => 30
        _ => 0
    if (D := G[set Count += 1; 4]):
        Print("{R} {Count} {C} {D}")
