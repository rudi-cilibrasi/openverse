small:=type{_X:int where 0<=_X,_X<=10}
fsmall:=type{_X:float where 0.0<=_X,_X<=10.0}
ShowInt(X:t where t:subtype(int))<computes>:string=ToString(X)
FormatInt(X:t where t:subtype(int))<computes>:string="[{X}]"
ShowFloat(X:t where t:subtype(float))<computes>:string=ToString(X)
ShowChar(X:t where t:subtype(char))<computes>:string="{X}"
ShowWide(X:t where t:subtype(char32))<computes>:string=ToString(X)
ShowString(X:t where t:subtype(string))<computes>:string="{X}"
ShowSmall(X:t where t:subtype(small))<computes>:string=ToString(X)
ShowSmallFloat(X:t where t:subtype(fsmall))<computes>:string="{X}"
Keep(X:t where t:subtype(int))<computes>:tuple(t,string)=(X,ToString(X))
Chars(A:[]a where a:subtype(char))<computes>:string=ToString(A)
WholeChars(A:t,Seed:a where a:subtype(char),t:subtype([]a))<computes>:string="{A}"
Relay(A:t,Seed:a where a:subtype(char),t:subtype([]a))<computes>:string=WholeChars(A,Seed)
AsString(S:string)<computes>:string=S
TupleChars(A:tuple(a,b) where a:subtype(char),b:subtype(char))<computes>:string=ToString(A)
Default(X:t,?Text:string=ToString(X) where t:subtype(int))<computes>:string=Text
holder(t:subtype(int)):=class<computes>:
    Value:t
    Get()<computes>:string="{Value}"
Method(B:holder(a) where a:subtype(int))<computes>:type{_()<computes>:string}=B.Get
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
