F(Items:[]t, Fallback:t where t:type)<computes>:t=
    for(Item:Items):
        for(J:=1..2):
            if(J=2):return Item|Fallback
    Fallback|Fallback
Main():void=
    for(V:=F(array{7,9},11)){Print("int {V}")}
    for(V:=F(array{"a","b"},"c")){Print("str {V}")}
    if(V:=F(array{7,9},11),V=11)then Print("first {V}")else Print("bad")
    for(V:=F(array{},13)){Print("empty {V}")}
