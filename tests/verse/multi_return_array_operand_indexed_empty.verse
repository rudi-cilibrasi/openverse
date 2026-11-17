Pure()<computes>:int=
    for(Index -> Item:array{}):return Index|Index+1
    99|100
WithWrite()<transacts>:int=
    var N:int=3
    for(Index -> Item:(block{set N+=10;array{}})):return Index|Index+1
    N|N+1
Main()<transacts>:void=
    for(V:=Pure()):Print("pure {V}")
    for(V:=WithWrite()):Print("write {V}")
