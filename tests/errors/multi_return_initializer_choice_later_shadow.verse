# expect: 4:4: 'Y' is already defined; Verse does not allow shadowing
F(X:int)<transacts>:int=
    Y:=if(X>2)then(return 0)else(X|X+1)
    Y:=100
    Y|Y+1
Main()<transacts>:void=for(V:=F(1)){Print("{V}")}
