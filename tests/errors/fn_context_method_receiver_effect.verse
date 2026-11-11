# expect: Run calls Touch, which has the effect <writes>
cell:=class{var N:int=0}
box:=class:
    C:cell
    Same(X:t where t:type)<computes>:t=X
Touch(B:box):box=
    set B.C.N+=1
    B
Apply(F:type{_(:t)<computes>:t},X:t where t:type)<computes>:t=F(X)
Run(B:box,X:t where t:type)<computes>:t=Apply(Touch(B).Same,X)
Main():void={}
