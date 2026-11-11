Two(N:int):int=N|N+1
Log(N:int):void=Print("event {N}")
Pick(X:t where t:type)<transacts>:t=
    E:=subscribable_event(int){}
    C:=E.Subscribe(Log)
    var Total:int=0
    defer:
        for(A:=(Two(0)|Two(2)),A=0,B:=(Two(0)|Two(2)),B=0):E.Signal(Total)
    if(A:=(Two(0)|Two(2)),B:=(Two(0)|Two(2)),set Total+=1,if(Total>0)then return X else 0,After:[]t=Concatenate()):
        Print("normal")
    X
Parameter(?N:int=Pick(7)):int=N
box(t:type):=class{Data:t;N:int=Pick(7)}
product:=class{N:int=0}
Make<constructor>() := product:
    N:=Pick(7)
blocked:=class:
    var N:int=0
    block:set N=Pick(7)
Cleanup():void=
    defer:Print("defer {Pick(7)}")
    Print("defer start")
Main():void=
    Print("parameter {Parameter()}")
    Print("field {box(string){Data:="tag"}.N}")
    Print("constructor {Make().N}")
    Print("block {blocked{}.N}")
    Cleanup()
