# Construction keeps the expected types of every field through projection.
dead(t:type) := struct<computes> { E:[]t=Concatenate(); V:int }
plain := struct<computes> { E:[]int=Concatenate(); V:int }
pack(a:type,b:subtype(comparable)) := struct<computes>:
    E:[]a = Concatenate()
    O:?a = false
    M:[b]a = map{}
    T:tuple(?a,[]b) = (false,Concatenate())
    V:a
    K:b
Get(X:t where t:type)<computes>:int = dead(t){V:=7}.V
Empty(X:t where t:type)<computes>:int = dead(t){V:=7}.E.Length
Value(X:a,Y:b where a:type,b:subtype(comparable))<computes>:a = pack(a,b){V:=X,K:=Y}.V
Key(X:a,Y:b where a:type,b:subtype(comparable))<computes>:b = pack(a,b){V:=X,K:=Y}.K
Swapped(X:b,Y:a where a:subtype(comparable),b:type)<computes>:b = Value(X,Y)
Nested(X:a,Y:b where a:type,b:subtype(comparable))<computes>:int = pack(a,b){V:=X,K:=Y}.T(1).Length
MapSize(X:a,Y:b where a:type,b:subtype(comparable))<computes>:int = pack(a,b){V:=X,K:=Y}.M.Length
Main():void =
    Print("plain {plain{V:=3}.V}")
    Print("generic {Get(7)} {Get("s")} {Empty(7)} {Empty("s")}")
    Print("values {Value(7,"s")} {Value("s",7)} {Key(7,"s")} {Key("s",7)}")
    Print("swapped {Swapped(7,"s")} {Swapped("s",7)}")
    Print("empty {Nested(7,"s")} {Nested("s",7)} {MapSize(7,"s")} {MapSize("s",7)}")
