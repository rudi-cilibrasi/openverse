holder:=struct:
    subscribable_event:int=7
    V:int=if(S:=subscribable_event[event(int){}]) then 1 else 0
Main():void=Print("{holder{}.V}")
