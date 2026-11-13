Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Choose(X:u,Y:v where t:type,u:subtype(t),v:subtype(t))<computes>:t=X
Main():void=
    Base:[]rational=array{}
    Value:tuple(int,int)=(7,8)
    R:=Upper(Base,Value)
    if(X:=R[0],Y:=R[1],X=7,Y=8):Print("tuple array 7 8 {R.Length}")
    B:[]any=array{}
    V:tuple(int,string)=(9,"tag")
    A:=Upper(B,V)
    Print("erased tuple array {A.Length}")
    NBase:[][]rational=array{}
    NValue:[]tuple(int,int)=array{(10,11)}
    N:=Upper(NBase,NValue)
    if(Row:=N[0],X:=Row[0],X=10):Print("nested tuple array 10 {Row.Length}")
    I:=Choose(Value,Base)
    if(X:=I[0],X=7):Print("inferred tuple array 7")
    J:=Choose(Base,Value)
    Print("inferred reverse {J.Length}")
