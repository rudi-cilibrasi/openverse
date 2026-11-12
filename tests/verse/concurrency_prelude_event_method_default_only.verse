holder:=class:
    Get(?X:int=block{E:=event(int){};E.Signal(1);7}):int=X
Main():void=Print("{holder{}.Get()}")
