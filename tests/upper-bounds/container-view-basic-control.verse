Array(A:[]int)<computes>:tuple([]int,int,int)=
    V:=if(X:=A[0])then X else -1
    (A,A.Length,V)
Methods(A:[]int)<computes>:tuple(int,int,int)=
    Last:=if(V:=A.Last[])then V else -1
    Sliced:=if(S:=A.Slice[0,1])then S.Length else -1
    (Last,Sliced,A.RemoveAllElements(7).Length)
Map(M:[int]int)<computes>:tuple([int]int,int,int)=
    V:=if(X:=M[1])then X else -1
    (M,M.Length,V)
Tuple(T:tuple(int,string))<computes>:tuple(tuple(int,string),int,string)=(T,T(0),T(1))
Option(O:?int)<computes>:int=if(V:=O?)then V else -1
Truth(L:logic)<computes>:logic=logic{L?}
Main():void=
    A:=Array(array{7,8})
    Print("array {A(1)} {A(2)} {A(0).Length}")
    B:=Methods(A(0))
    Print("methods {B(0)} {B(1)} {B(2)}")
    M:=Map(map{1=>9})
    Print("map {M(1)} {M(2)}")
    T:=Tuple((7,"s"))
    Print("tuple {T(1)} {T(2)} {T(0)(1)}")
    Print("option {Option(option{7})} {Option(false)}")
    Yes:logic=true
    No:logic=false
    if(Truth(Yes)?)then Print("logic true")else Print("bad")
    if(Truth(No)?)then Print("bad")else Print("logic false")
