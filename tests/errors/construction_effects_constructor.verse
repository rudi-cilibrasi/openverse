# expect: declared construction budget
box(t:type):=class<reads>{Value:t}
Make<constructor>(X:t where t:type)<computes>:=box(t):Value:=X
Main():void={}
