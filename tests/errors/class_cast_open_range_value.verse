# expect: would name what is unknown (#250)
# A bound may open a hidden argument to read an int, but an element cannot
# export an option whose type names that argument.
base(t:type):=class:
    Value:t
pair(t:type,u:type):=class(base(t)):
    Other:u
    Lo:int=0
    Hi:int=1
Main():void=
    B:base(int)=pair(int,string){Value:=1,Other:="o"}
    X:=for(I:=pair[B].Lo..pair[B].Hi){(I,option{pair[B].Other})}
    Print("{X.Length}")
