# expect: expected b, found a
# A conditional field's cast stays in its branch even when another field
# has a mandatory cast that is lifted from the same constructor.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){C:int=4}
box:=class{First:int;Second:int}
Bad(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<decides>:b=
    X:=box{First:=if(D:=dup[P])then D.C else 0,Second:=dup[Q].C}
    P.A
Main():void={}
