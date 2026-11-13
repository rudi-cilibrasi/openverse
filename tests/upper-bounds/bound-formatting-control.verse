small:=type{_X:int where 0<=_X,_X<=10}
fsmall:=type{_X:float where 0.0<=_X,_X<=10.0}
ShowInt(X:int)<computes>:string=ToString(X)
FormatInt(X:int)<computes>:string="[{X}]"
ShowFloat(X:float)<computes>:string=ToString(X)
ShowChar(X:char)<computes>:string="{X}"
ShowWide(X:char32)<computes>:string=ToString(X)
ShowString(X:string)<computes>:string="{X}"
ShowSmall(X:small)<computes>:string=ToString(X)
ShowSmallFloat(X:fsmall)<computes>:string="{X}"
Keep(X:small)<computes>:tuple(small,string)=(X,ToString(X))
Chars(A:string)<computes>:string=ToString(A)
WholeChars(A:string,Seed:char)<computes>:string="{A}"
Relay(A:string,Seed:char)<computes>:string=WholeChars(A,Seed)
AsString(S:string)<computes>:string=S
TupleChars(A:tuple(char,char))<computes>:string=ToString(AsString(A))
Default(X:int,?Text:string=ToString(X))<computes>:string=Text
holder(t:type):=class<computes>:
    Value:int
    Get()<computes>:string="{Value}"
Method(B:holder(a) where a:type)<computes>:type{_()<computes>:string}=B.Get
Main():void=
    Print("integer {ShowInt(7)} {FormatInt(7)}")
    Print("scalars {ShowFloat(2.5)} {ShowChar('z')} {ShowWide(0u03BB)} {ShowString("text")}")
    S:small=3
    F:fsmall=2.5
    K:=Keep(S)
    Precise:small=K(0)
    Print("refined {ShowSmall(S)} {ShowSmallFloat(F)} precise {Precise} {K(1)}")
    A:=array{'o','k'}
    Print("characters {Chars(A)} {Relay(A,'o')} {TupleChars(('h','i'))}")
    Empty:[]char=array{}
    Print("empty '{Relay(Empty,'z')}'")
    H:=holder(small){Value:=S}
    Read:=Method(H)
    Print("default {Default(S)} method {Read()}")
