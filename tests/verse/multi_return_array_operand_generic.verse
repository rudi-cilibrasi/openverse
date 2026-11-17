F(Items:[]t,Default:t,N:int where t:type)<computes>:t=
    for(Item:Items):
        return Item|Default
    Default|Default
Main():void=
    for(V:=F(array{4,7},9,1)){Print("int {V}")}
    for(V:=F(array{"a","b"},"c",1)){Print("str {V}")}
    if(V:=F(array{4,7},9,1),V=9)then Print("first {V}")else Print("bad")
