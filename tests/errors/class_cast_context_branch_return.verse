# expect: return is not allowed in a branch (Book of Verse ch. 14)
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){C:int=4}
Run(P:pair(a,b) where a:type,b:type)<suspends>:void=
    branch:if(D:=dup[P])then block{return 7;D.C}else 0
Main()<suspends>:void=Run(dup(int){})
