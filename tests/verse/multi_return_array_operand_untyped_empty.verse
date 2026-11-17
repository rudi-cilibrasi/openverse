Pure()<computes>:int=
    for(Item:array{}):return 1|2
    99|100
WithWrite()<transacts>:int=
    var N:int=3
    for(Item:(block{set N+=10;array{}})):return 1|2
    N|N+1
Main()<transacts>:void=
    for(V:=Pure()){Print("pure {V}")}
    for(V:=WithWrite()){Print("write {V}")}
