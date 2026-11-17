# expect: 6:8: unknown identifier 'Z'
F(X:int)<transacts>:int=
    Y:=if(X>2)then(return 0)else block:
        Z:=X*10
        Z|Z+1
    Y|Y+Z
Main()<transacts>:void=for(V:=F(1)){Print("{V}")}
