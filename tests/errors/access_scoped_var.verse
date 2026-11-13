# expect: Count of Gameplay.stock cannot be set here: its var is scoped to Gameplay, Inventory: only code there may use it
# (Book of Verse ch. 12, "Scoped Read or Write Access")
Gameplay := module:
    stock<public> := class:
        var<scoped{Inventory}> Count<public>:int = 0
Inventory := module{}
Main():void =
    S := Gameplay.stock{}
    set S.Count = 3
