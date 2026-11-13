Same(X:int)<computes>:int=
    if(X=X)then X else Err()
Main():void=
    R:=Same(7)
    Print("{R}")
