# expect: cheap cannot be below Shop.item, as subclassing constructs it: the constructor of Shop.item is internal to Shop
# (ArchetypeAccessSpecifiers.versetest:22: "you cannot get around the restrictions by using subclassing")
Shop := module:
    item<public> := class<internal>:
        Price<public>:int = 1
cheap := class(Shop.item){}
Main():void = {}
