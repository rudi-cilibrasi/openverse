# expect: a range's values are ints: I:string
Bounds()<computes>:int=1|2
Pick()<computes>:int=
    for(I:string:=Bounds()..2):
        return 1|2
    3|4
Main():void=for(V:=Pick()):Print("{V}")
