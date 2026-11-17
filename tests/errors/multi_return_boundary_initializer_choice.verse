# expect: 2:0: F has several values and a return in a loop or binding initializer whose expression is not single-valued or starts concurrent work: not supported yet (#686, #687)
F(X:int)<transacts>:int=
    Y:=if(X>2)then(return 0)else(X|X+1)
    Y|Y+1
Main()<transacts>:void=for(V:=F(3)){Print("{V}")}
