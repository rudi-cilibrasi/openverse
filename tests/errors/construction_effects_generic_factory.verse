# expect: declared construction budget
box(t:type):=class<reads>{Value:t}
Make(X:t where t:type)<computes>:box(t)=box(t){Value:=X}
Main():void={}
