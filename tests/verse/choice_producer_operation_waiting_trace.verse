link:=class<unique>:
    Code:int
    Next:?link
trace:=class<unique>:
    var Head:?link=false
    Note(Code:int)<transacts>:void=set Head=option{link{Code:=Code,Next:=Head}}
a:=class<computes>:
    T:trace
    N:int=1
    M()<transacts>:int=
        T.Note(101)
        defer{T.Note(119)}
        (block{T.Note(111);N})|(block{T.Note(112);N+10})
b:=class<computes>:
    T:trace
    N:int=2
    M()<transacts>:int=
        T.Note(201)
        defer{T.Note(219)}
        (block{T.Note(211);N})|(block{T.Note(212);N+10})
Dup(V:t where t:type)<computes>:t=V|V
Main()<suspends>:void=
    T:=trace{}
    Rows:=for(A0:=Dup(a{T:=T})|Dup(b{T:=T}),X0:=A0.M(),A1:=Dup(a{T:=T})|Dup(b{T:=T}),X1:=A1.M(),A2:=Dup(a{T:=T})|Dup(b{T:=T}),X2:=A2.M(),A3:=Dup(a{T:=T})|Dup(b{T:=T}),X3:=A3.M()):
        Score:=X0+A0.N+X1+A1.N+X2+A2.N+X3+A3.N
        defer{T.Note(500+Score)}
        T.Note(300+Score)
        Sleep(0.001)
        T.Note(400+Score)
        Score
    var Sum:int=0
    for(R:Rows):set Sum+=R
    var Cursor:?link=T.Head
    var Chunk:string=""
    var Used:int=0
    loop:
        if(Current:=Cursor?):
            set Chunk+="{Current.Code},"
            set Used+=1
            set Cursor=Current.Next
            if(Used=128):
                Print(Chunk)
                set Chunk=""
                set Used=0
        else:
            if(Used>0):Print(Chunk)
            break
    Print("{Rows.Length} {Sum}")
