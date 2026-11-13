component:=class<computes><castable>{Power:int=1}
warrior:=class<computes>(component){Name:string="w"}
Strongest(Xs:[]t where t:castable_subtype(component))<transacts><decides>:t=
    var Best:int=0
    for(I->X:Xs, X.Power>Xs[Best].Power):
        set Best=I
    Xs[Best]
holder(t:castable_subtype(component)):=class<computes>:
    Item:t
    Power()<computes>:int=Item.Power
    Get()<computes>:t=Item
Wrap(X:t where t:castable_subtype(component))<computes>:holder(t)=holder(t){Item:=X}
Main():void=
    if(W:=Strongest[array{warrior{Power:=2,Name:="a"},warrior{Power:=5,Name:="b"},warrior{Power:=3}}]):
        Print("strongest {W.Name} {W.Power}")
    H:=Wrap(warrior{Power:=7,Name:="c"})
    Print("holder {H.Power()} {H.Get().Name}")
    C:=Wrap(component{Power:=4})
    Print("component {C.Power()}")
