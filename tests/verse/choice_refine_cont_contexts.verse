# Continuations of fors whose first clause is a refining choice and whose
# next has a choice too: reached at two type instances, in a parameter's
# default, in an interface's default copied into two classes, in a
# function with several values inlined at two sites, and two fors with
# returns on one line, alone and nested
pair(a:type,b:type) := class { A:a; B:b }
dup(t:type) := class(pair(t,t)) { C:int=4 }
Find(P:pair(a,b),X:t where a:type,b:type,t:type):[]int =
    for(V0:=if(D:=dup[P])then(D.C|D.C+1)else 0,V1:=(V0|V0*10),V1>4):
        W:[]t=array{X,X}
        V1+W.Length
Show(R:[]int):string = "{R.Length} {R[0] or -1} {R[1] or -1} {R[2] or -1}"
Count(P:pair(a,b),?N:int=(for(V0:=if(D:=dup[P])then(D.C|D.C+1)else 0,V1:=(V0|V0*10),V1>4){V1}).Length where a:type,b:type):int = N
counter(t:type) := interface:
    Tally(P:pair(a,b),X:t where a:type,b:type):int =
        R:=for(V0:=if(D:=dup[P])then(D.C|D.C+1)else 0,V1:=(V0|V0*10),V1>4){W:[]t=array{X};V1+W.Length}
        R.Length*1000+(R[0] or -1)
c1 := class(counter(int)){}
c2 := class(counter(string)){}
Pick(P:pair(a,b) where a:type,b:type)<transacts>:int =
    R:=for(V0:=if(D:=dup[P])then(D.C|D.C+1)else 0,V1:=(V0|V0*10),V1>4){V1}
    R.Length|R.Length*100
Same(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type):int = block{for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0){if(A>4){return A}}; for(B:=if(E:=dup[Q])then(E.C|E.C+1)else 0){if(B>3){return B*100}}; 0}
Nest(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type):int = block{for(A:=if(D:=dup[P])then(D.C|D.C+1)else 0){for(B:=if(E:=dup[Q])then(E.C|E.C+1)else 0){if(A+B>8){return A*10+B}}}; -1}
Main()<transacts>:void=
    Y:pair(int,int)=dup(int){A:=1,B:=2}
    S:pair(string,string)=dup(string){A:="a",B:="b"}
    Z:pair(int,string)=pair(int,string){A:=1,B:="x"}
    W:pair(int,int)=pair(int,int){A:=1,B:=2}
    Print("{Show(Find(Y,7))} | {Show(Find(S,"s"))} | {Show(Find(Z,7))}")
    Print("{Count(Y)} {Count(S)} {Count(W)} {Count(Y,?N:=9)}")
    T1:counter(int)=c1{}
    T2:counter(string)=c2{}
    Print("{T1.Tally(Y,1)} {T2.Tally(S,"s")} {T2.Tally(Z,"s")}")
    for(X:=Pick(Y),U:=Pick(W)){Print("pick {X} {U}")}
    Print("{Same(Y,Y)} {Same(Z,S)} {Same(Z,Z)} {Nest(Y,S)} {Nest(Z,Y)}")
