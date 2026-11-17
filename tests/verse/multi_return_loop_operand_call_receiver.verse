# A resolved call result stays an ordinary receiver when a lazy range
# consumer shares analysis with a mutable callable local.
Inner:=class{Work:type{_()<computes>:int}}
Outer:=class{Box:Inner}
MakeBox(H:Outer)<computes>:Inner=H.Box
One()<computes>:int=11
Caller(H:Outer,F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<transacts>:type{_()<computes>:int}=
    var Stored:type{_()<computes>:int}=Dummy
    for(I:=1..N):
        set Stored=Dummy
        X:=MakeBox(H).Work()
        if(I=2):return Stored|Stored
    F|F
Wrap(H:Outer,F:type{_()<computes>:int},Dummy:type{_()<computes>:int},N:int)<transacts>:void=
    for(G:=Caller(H,F,Dummy,N)):
        Print("row")
Main()<transacts>:void=Wrap(Outer{Box:=Inner{Work:=One}},One,One,3)
