F(Original:[]t,Fallback:t where t:type)<transacts>:t=
    var Items:[]t=Original
    for(Index -> Item:Items):
        Print("row {Index}")
        defer:Print("cleanup {Index}")
        set Items=array{Fallback}
        if(Index=1):return Item|(Items[0] or Fallback)
    Fallback|Fallback
Positions()<computes>:int=
    for(Index -> Item:array{4,7,9}):
        if(Item=7):return Index|Index+1
    99|100
Main()<transacts>:void=
    for(V:=F(array{4,7,9},99)):Print("int {V}")
    for(V:=F(array{"a","b","c"},"z")):Print("string {V}")
    if(V:=F(array{4,7,9},99),V=99)then Print("first {V}")else Print("bad")
    if(V:=F(array{4,7,9},99),V=-1)then Print("bad")else Print("none")
    for(V:=F(array{4},77)):Print("short {V}")
    for(V:=Positions()):Print("index {V}")
