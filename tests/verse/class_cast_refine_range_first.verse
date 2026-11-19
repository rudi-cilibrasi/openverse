# The parser's first-range producer must not hide its bound casts from the
# remaining clauses. Explicit named casts agree at the full generic result.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)):
    Lo:int=1
    Hi:int=2
Direct(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=
    first{I:=dup[P].Lo+0..dup[Q].Hi+0;I>1;X:b=P.A;Y:d=Q.A;(I,X,Y)}
Named(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=
    first{D:=dup[P];E:=dup[Q];I:=D.Lo+0..E.Hi+0;I>1;X:b=P.A;Y:d=Q.A;(I,X,Y)}
Prefix(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=
    first{Offset:=(0|1);I:=Offset+dup[P].Lo..Offset+dup[Q].Hi;I>2;X:b=P.A;Y:d=Q.A;(I,X,Y)}
PrefixNamed(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:tuple(int,b,d)=
    first{Offset:=(0|1);D:=dup[P];E:=dup[Q];I:=Offset+D.Lo..Offset+E.Hi;I>2;X:b=P.A;Y:d=Q.A;(I,X,Y)}
Lower(P:pair(a,b) where a:type,b:type)<transacts><decides>:int=first{I:=dup[P].Lo..3;I>1;I}
Upper(P:pair(a,b) where a:type,b:type)<transacts><decides>:int=first{I:=0..dup[P].Hi;I>1;I}
Main():void=
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    Bad:pair(int,string)=pair(int,string){A:=1,B:="other"}
    if(V:=Direct[P,Q],W:=Named[P,Q]) then Print("first {V(0)} {V(1)} {V(2)} / {W(0)} {W(1)} {W(2)}") else Print("wrong")
    if(V:=Prefix[P,Q],W:=PrefixNamed[P,Q]) then Print("prefix {V(0)} {V(1)} {V(2)} / {W(0)} {W(1)} {W(2)}") else Print("wrong prefix")
    if(L:=Lower[P],U:=Upper[P]) then Print("sides {L} {U}")
    if(V:=Direct[Bad,Q]) then Print("wrong") else Print("missing lower")
    if(V:=Direct[P,Bad]) then Print("wrong") else Print("missing upper")
    if(V:=Direct[dup(int){A:=7,B:=9,Lo:=3},Q]) then Print("wrong") else Print("empty")
