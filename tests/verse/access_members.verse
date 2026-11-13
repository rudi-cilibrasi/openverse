# Access to a class's members (Book of Verse ch. 12, docs/research/access-specifiers.md): <private>
# for the class's own code, <protected> for it and the classes below it, internal for its module,
# <public> for all; var<…> X<…> reads and writes apart; class<internal> constructs only in its module.
Store := module:
    inventory<public> := class<internal>:
        var<private> Items<public>:[]string = array{}
        Capacity<private>:int = 2
        AddItem<public>(Name:string)<transacts><decides>:void =
            HasRoom[]
            set Items += array{Name}
        HasRoom<private>()<reads><decides>:void = Items.Length < Capacity
        Count<public>()<reads>:int = Items.Length
    MakeInventory<public>():inventory = inventory{}
    Peek<public>(I:inventory):int = I.Count()

game_entity := class:
    var Health<protected>:int = 100
    Damage<protected>(Amount:int):void = set Health -= Amount
player := class(game_entity):
    TakeHit():void =
        Damage(25)
        set Health += 5
    Report():int = Health
resource := class:
    var<private> Available<public>:int = 1000
    Allocate<public>(Amount:int)<transacts><decides>:void =
        Amount <= Available
        set Available -= Amount
Main():void =
    Bag := Store.MakeInventory()
    if (Bag.AddItem["sword"], Bag.AddItem["shield"], not Bag.AddItem["bow"]):
        Print("{Bag.Count()} {Bag.Items.Length}")
    Hero := player{}
    Hero.TakeHit()
    Print("{Hero.Report()}")
    R := resource{}
    if (R.Allocate[400]) then Print("{R.Available}")
