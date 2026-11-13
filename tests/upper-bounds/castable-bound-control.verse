component:=class<computes><castable>{Power:int=1}
warrior:=class<computes>(component){Name:string="w"}
Strongest(Xs:[]warrior)<transacts><decides>:warrior=
    var Best:int=0
    for(I->X:Xs, X.Power>Xs[Best].Power):
        set Best=I
    Xs[Best]
holder:=class<computes>:
    Item:warrior
    Power()<computes>:int=Item.Power
    Get()<computes>:warrior=Item
cholder:=class<computes>:
    Item:component
    Power()<computes>:int=Item.Power
Main():void=
    if(W:=Strongest[array{warrior{Power:=2,Name:="a"},warrior{Power:=5,Name:="b"},warrior{Power:=3}}]):
        Print("strongest {W.Name} {W.Power}")
    H:=holder{Item:=warrior{Power:=7,Name:="c"}}
    Print("holder {H.Power()} {H.Get().Name}")
    C:=cholder{Item:=component{Power:=4}}
    Print("component {C.Power()}")
