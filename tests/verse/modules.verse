# modules (#112): nesting, qualified access, using{M}, a module's enum and class
melee := module:
    Bonus<public>:int = 2
    Base:int = 10
    Damage<public>(X:int):int = X + Bonus + Base

spell := module:
    Bonus<public>:int = 3
    Inner<public> := module:
        Factor<public>:int = 7
        Scale<public>(X:int):int = X * Factor
    color<public> := enum:
        Red
        Blue
    wand<public> := class:
        Power<public>:int
        Cast<public>():int = Power * Inner.Factor

using{spell}

Total():int = melee.Bonus + spell.Bonus

Main():void =
    Print("{Total()} {melee.Damage(1)}")
    Print("{spell.Inner.Scale(2)} {Inner.Scale(3)}")
    W := spell.wand{Power := 2}
    Print("{W.Cast()}")
    C:spell.color = spell.color.Blue
    if (C = color.Blue) then Print("blue")
    V:wand = wand{Power := 1}
    Print("{V.Cast()}")
