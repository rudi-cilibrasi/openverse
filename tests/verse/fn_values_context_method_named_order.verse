box:=class:
    Same(X:t where t:type)<computes>:t=X
applicator:=class:
    Apply(?F:type{_(:u)<computes>:u},?X:u where u:subtype(comparable))<computes>:int=if(F(X)=X)then 1 else -1
Run(A:applicator,B:box,X:t where t:subtype(comparable))<computes>:int=A.Apply(?F:=B.Same,?X:=X)
Main():void=Print("{Run(applicator{},box{},7)}")
