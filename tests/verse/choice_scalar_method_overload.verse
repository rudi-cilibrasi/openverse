Tell(S:string,V:int):int=
    Print(S)
    V

probe:=class:
    Many(N:int):int=N|(N+1)
    Many(A:int,B:int):int=A*10+B
    Run():void=
        Print("scalar direct")
        A:=for{X:=Tell("wrong scalar prefix",0)+(1|2);Y:=Self.Many(0,1);false?;X+Y}
        Print("{A.Length}")
        Print("scalar nested")
        B:=for{X:=Tell("wrong nested prefix",0)+(1|2);logic{Y:=Self.Many((0|1),(0|1));false?}?;X}
        Print("{B.Length}")
        Print("scalar alternative")
        C:=for{X:=Tell("wrong alternative prefix",0)+(Self.Many(0,1)|2);false?;X}
        Print("{C.Length}")
        Print("many direct")
        D:=for{X:=Tell("many direct prefix",0)+(1|2);Y:=Many(0);false?;X+Y}
        Print("{D.Length}")
        Print("many nested")
        E:=for{X:=Tell("many nested prefix",0)+(1|2);logic{Y:=Many(0);false?}?;X}
        Print("{E.Length}")

Main():void=probe{}.Run()
