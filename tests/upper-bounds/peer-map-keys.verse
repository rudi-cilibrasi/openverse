Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Choose(X:u,Y:v where t:type,u:subtype(t),v:subtype(t))<computes>:t=X
key_base:=class<unique><allocates>{}
key_child:=class<allocates>(key_base){}
Main():void=
    Base:[rational]rational=map{}
    Value:[int]int=map{2=>7,1=>8}
    M:=Upper(Base,Value)
    if(V:=M[2],V=7):Print("widened keys 7 {M.Length}")
    N:=Choose(Value,Base)
    if(V:=N[1],V=8):Print("inferred keys 8 {N.Length}")
    E:[int]int=map{}
    Empty:=Upper(Base,E)
    Print("empty keys {Empty.Length}")
    TupleBase:[tuple(rational,string)]rational=map{}
    TupleValue:[tuple(int,string)]int=map{(3,"t")=>9}
    TupleMap:=Upper(TupleBase,TupleValue)
    if(V:=TupleMap[(3,"t")],V=9):Print("tuple keys 9")
    K:=key_child{}
    NominalBase:[key_base]int=map{}
    NominalValue:[key_child]int=map{K=>10}
    NominalMap:=Upper(NominalBase,NominalValue)
    if(V:=NominalMap[K]):Print("nominal keys {V}")
