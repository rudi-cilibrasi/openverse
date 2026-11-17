# expect: 2:0: F has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
F(X:int)<transacts>:int=
    for(I:=1..X):
        if(I=2):return I|I+1
    X|X+1
Main()<transacts>:void=for(V:=F(3)){Print("{V}")}
