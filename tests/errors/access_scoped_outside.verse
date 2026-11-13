# expect: Gameplay.Make is scoped to Gameplay, Inventory: only code there may use it
# (Book of Verse ch. 12, "Cross-Module Collaboration": only the listed modules)
Gameplay := module:
    Make<scoped{Inventory}>(N:int):int = N
Inventory := module{}
Shop := module:
    Buy<public>():int = Gameplay.Make(2)
Main():void = Print("{Shop.Buy()}")
