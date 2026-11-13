# modules (#112): lexical lookup, constructors, qualified methods, braced and empty modules
settings := struct:
    Speed:int = 5
Config := module:
    Speed<public>:int = 99
Game := module:
    # (Game's own Config, a value, comes before the module Config)
    (Game:)Config:settings = settings{}
    Get<public>():int = Config.Speed
Lib := module:
    (Lib:)Fact<public>(N:int):int = 0
    base<public> := class:
        W<public>:int = 0
    MakeBase<public><constructor>(X:int) := base:
        W := X
    MakeBase2<public><constructor>() := base:
        MakeBase<constructor>(5)
using{Lib}
# (the file's own Fact comes before the open module's)
Fact(N:int):int = if (N <= 1) then 1 else N * Fact(N - 1)
MakeBase3<constructor>() := Lib.base:
    Lib.MakeBase<constructor>(7)
Q := module:
    i1<public> := interface:
        M<public>():int
    i2<public> := interface:
        M<public>():int
    c<public> := class(i1, i2):
        (i1:)M<override>():int = 1
        (i2:)M<override>():int = 2
        Both<public>():int = 10 * (i1:)M() + (i2:)M()
Braced := module {
    X<public>:int = 1; Y<public>:int = 2
    Inner<public> := module { Z<public>:int = 3 }
    using{Inner}
    using { /Verse.org/Simulation }
    W<public>:int = Z + 1
}
Empty := module:
Main():void =
    Print("{Game.Get()} {Fact(5)} {Lib.Fact(5)}")
    B2 := Lib.MakeBase2()
    B3 := MakeBase3()
    Print("{B2.W} {B3.W}")
    X := Q.c{}
    A:Q.i1 = X
    Print("{A.M()} {X.Both()} {X.(Q.i1:)M()} {X.(Q.i2:)M()}")
    Print("{Braced.X + Braced.Y} {Braced.W}")
