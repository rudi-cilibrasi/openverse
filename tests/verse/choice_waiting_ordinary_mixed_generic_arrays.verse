Two(N:int)<computes>:int=N|N+1
Early(N:int)<computes>:int=
    if(N<0):return 0
    N|N+1
Run(X:t where t:type)<suspends>:[]tuple(int,int,[]t)=
    for(A:=Early(1),A=1,B:=(Two(10)|Two(20)),B=10,C:=Early(30),C=30):
        Sleep(0.01)
        Written:[]?t=array{}
        (A,B,array{X})
Main()<suspends>:void=
    Ints:=Run(7)
    for(Row:Ints,V:Row(2)):Print("generic {Row(0)} {Row(1)} {V}")
    Strings:=Run("x")
    for(Row:Strings,V:Row(2)):Print("generic {Row(0)} {Row(1)} {V}")
