Box:=class{N:int}
Cell(N:int)<transacts>:Box=
    if(N<=0)then(Box{N:=1}|Box{N:=2})else:
        var K:int=0
        X:=Cell(N-1)
        set K+=X.N
        if(Cell(N-1).N>K){set K+=100}
        Box{N:=K}
Main()<transacts>:void=for(V:=Cell(2)){Print("{V.N}")}
