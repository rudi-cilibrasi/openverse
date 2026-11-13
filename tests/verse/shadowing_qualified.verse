# Shadowing (Book of Verse ch. 10, "Shadowing and Qualification"): a
# definition may take the name of one around it only qualified, saying where
# it is: a module's member or submodule, a class's field or method, an enum's
# value, a (local:) parameter; a function also when no call fits both
Value:int = 1
F():int = 100
Top := module:
    (Top:)Value<public>:int = 2
    F<public>(X:int):int = X + 1              # F() and F(X:int): overloads
    Inner<public> := module:
        (Top.Inner:)Inner<public> := module:  # a module named like its own
            (Top.Inner.Inner:)Value<public>:int = 3
box := class:
    (box:)Value:int = 4
    (box:)F():int = 5
    Sum():int = (box:)Value + (box:)F() + Self.Value
kind := enum{(kind:)kind, Other}
Scale((local:)Value:int):int = 10 * (local:)Value
Main():void =
    Print("{Value} {Top.Value} {Top.Inner.Inner.Value} {(Top.Inner.Inner:)Value} {Top.F(6)} {F()}")
    Print("{box{}.Sum()} {box{}.F()} {Scale(7)}")
    if ((kind:)kind <> kind.Other) then Print("an enum's value named like its enum, qualified")
