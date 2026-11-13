# <scoped{…}> access (Book of Verse ch. 12, "Scoped"; docs/research/access-specifiers.md): a
# definition scoped to modules is used in them, besides its own; an access level may be named,
# S := scoped{A, B}; a member keeps its own access, so it is scoped too to be used there.
Gameplay := module:
    SharedGameplayScope := scoped{Inventory, Crafting}
    item<SharedGameplayScope> := class:
        ID<public>:int
    CreateItem<SharedGameplayScope>(TheID:int):item = item{ID := TheID}
Inventory := module:
    using{Gameplay}
    AddToInventory<public>(ItemID:int):int = CreateItem(ItemID).ID
Crafting := module:
    using{Gameplay}
    CraftItem<public>(Recipe:[]int)<decides>:int = CreateItem(Recipe[0]).ID
Graphics := module:
    shape<scoped{Physics}> := class:
        Size<scoped{Physics}>:int = 1
Physics := module:
    using{Graphics}
    Report<public>():int =
        S := shape{}
        S.Size
Main():void =
    Print("{Inventory.AddToInventory(7)} {Physics.Report()}")
    if (X := Crafting.CraftItem[array{3}]) then Print("{X}")
