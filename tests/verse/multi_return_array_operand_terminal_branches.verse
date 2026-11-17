F(Items:[]int,Flag:logic)<computes>:int=
    for(Item:Items):
        if(Flag?)then return Item|Item+1 else return Item+10|Item+11
    0|1
Main():void=
    for(V:=F(array{3,9},true)){Print("true {V}")}
    for(V:=F(array{3,9},false)){Print("false {V}")}
    for(V:=F(array{},false)){Print("empty {V}")}
