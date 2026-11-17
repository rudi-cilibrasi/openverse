F()<transacts>:int=
    var Items:[]int=array{4,7,9}
    for(Item:Items):
        Print("row {Item}")
        set Items=array{99}
        if(Item=7):return Item|(Items[0] or -1)
    111|112
Main():void=
    for(V:=F()){Print("value {V}")}
    if(V:=F(),V=99)then Print("first {V}")else Print("bad")
