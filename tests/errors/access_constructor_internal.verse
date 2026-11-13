# expect: Shop.item{…} constructs Shop.item here: the constructor of Shop.item is internal to Shop
# (ArchetypeAccessSpecifiers.versetest:15: class<internal> "forces folks outside the owning module to use a constructor function")
Shop := module:
    item<public> := class<internal>:
        Price<public>:int
    Make<public>(P:int):item = item{Price := P}
Main():void =
    Print("{Shop.Make(3).Price}")
    X := Shop.item{Price := 4}
