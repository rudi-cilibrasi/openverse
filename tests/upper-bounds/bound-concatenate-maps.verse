small:=type{_X:int where 0<=_X,_X<=10}
Whole(A:t,B:u where t:subtype([int]int),u:subtype([int]int))<computes>:[int]int=(R:=ConcatenateMaps(A,B);R)
Values(A:[int]a,B:[int]b where a:subtype(int),b:subtype(int))<computes>:[int]int=(R:=ConcatenateMaps(A,B);R)
Keys(A:[a]int,B:[b]int where a:subtype(rational),b:subtype(rational))<computes>:[rational]int=(R:=ConcatenateMaps(A,B);R)
Discard(A:t,B:u where t:subtype([void]int),u:subtype([void]int))<computes>:[void]int=(R:=ConcatenateMaps(A,B);R)
DropKeys(A:[int]int)<computes>:[void]int=A
Main():void=
    A:[int]int=map{1=>10,2=>20}
    B:[int]int=map{2=>30,3=>40}
    W:=Whole(A,B)
    if(W=map{1=>10,2=>30,3=>40})then Print("whole order {W.Length}")
    S:small=3
    M:[int]small=map{1=>S,2=>S}
    V:=Values(M,map{2=>7,3=>9})
    if(V=map{1=>3,2=>7,3=>9})then Print("value order {V.Length}")
    One:rational=1
    Two:rational=2
    Three:rational=3
    N:[rational]int=map{Two=>30,Three=>40}
    K:=Keys(A,N)
    if(K=map{One=>10,Two=>30,Three=>40},X:=K[Two])then Print("key order {K.Length} {X}")
    Empty:[int]int=map{}
    Print("empty {Whole(Empty,Empty).Length}")
    DA:[int]int=map{1=>10,2=>20}
    DB:[int]int=map{3=>30}
    D:=Discard(DA,DB)
    Expected:=DropKeys(map{1=>30,2=>20})
    Unit:void=()
    if(D=Expected,X:=D[Unit])then Print("discard {D.Length} {X}")
