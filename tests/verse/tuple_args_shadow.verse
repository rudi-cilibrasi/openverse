# Tuple expansion follows local, method and field lookup before top-level signatures.
Pick(A:int,B:int):int = A+B
Tuple(P:tuple(int,int)):int = P(0)*10+P(1)
Use(Pick:type{_(:tuple(int,int)):int}):int = Pick((2,3))
box := class:
    (box:)Pick(P:tuple(int,int)):int = P(0)*100+P(1)
    Run():int = (box:)Pick((2,3))
fieldbox := class:
    (fieldbox:)Pick:type{_(:tuple(int,int)):int}
    Run():int = (fieldbox:)Pick((2,3))
Main():void =
    Print("{Use(Tuple)} {box{}.Run()} {fieldbox{Pick:=Tuple}.Run()}")
