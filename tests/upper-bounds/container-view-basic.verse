Array(A:t where t:subtype([]int))<computes>:tuple(t,int,int)=
    V:=if(X:=A[0])then X else -1
    (A,A.Length,V)
Methods(A:t where t:subtype([]int))<computes>:tuple(int,int,int)=
    Last:=if(V:=A.Last[])then V else -1
    Sliced:=if(S:=A.Slice[0,1])then S.Length else -1
    (Last,Sliced,A.RemoveAllElements(7).Length)
Map(M:t where t:subtype([int]int))<computes>:tuple(t,int,int)=
    V:=if(X:=M[1])then X else -1
    (M,M.Length,V)
Tuple(T:t where t:subtype(tuple(int,string)))<computes>:tuple(t,int,string)=(T,T(0),T(1))
Option(O:t where t:subtype(?int))<computes>:int=if(V:=O?)then V else -1
Truth(L:t where t:subtype(logic))<computes>:logic=logic{L?}
Main():void=
    A:=Array(array{7,8})
    Print("array {A(1)} {A(2)} {A(0).Length}")
    B:=Methods(A(0))
    Print("methods {B(0)} {B(1)} {B(2)}")
    M:=Map(map{1=>9})
    Print("map {M(1)} {M(2)}")
    T:=Tuple((7,"s"))
    Print("tuple {T(1)} {T(2)} {T(0)(1)}")
    Empty:?int=false
    Print("option {Option(option{7})} {Option(Empty)}")
    Yes:logic=true
    No:logic=false
    if(Truth(Yes)?)then Print("logic true")else Print("bad")
    if(Truth(No)?)then Print("bad")else Print("logic false")
