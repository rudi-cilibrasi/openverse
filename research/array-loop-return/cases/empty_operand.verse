Empty(Item:int)<computes><decides>:int=if(false?)then Item|Item+1 else false?
ArrayReturn()<computes><decides>:int=
    for(Item:array{4,7,9}):
        if(Item=7):return Empty[Item]
        if(Item=9):Err()
    Err()
Main():void=
    if(V:=ArrayReturn[])then Print("bad value {V}")else Print("none")
    if(V:=option{ArrayReturn[]}?)then Print("bad option {V}")else Print("option none")
    for(V:=first{ArrayReturn[]}){Print("bad first {V}")}
    Print("after")
