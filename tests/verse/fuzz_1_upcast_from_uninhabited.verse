# internal error: G does not pass Prog.checkTypes. i6 has no class below it
# (so G is unreachable, which LANGUAGE.md says is accepted), but i2 does (c);
# the upcast of an i6 to an i2 is ill-typed in the elaborated Core.
i2 := interface:
    V:int = 1
i6 := interface(i2):
    W:int = 2
G(X:i6):i2 = X
c := class(i2):
    U:int = 0
Main():void =
    Print("x")
