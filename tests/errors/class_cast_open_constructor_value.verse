# expect: expected int, found u'
# Opening a hidden argument supplies no equation making it int.
base(t:type):=class{Value:t}
pair(t:type,u:type):=class(base(t)){Other:u}
box:=class{Value:int}
Bad(B:base(int))<decides>:box=box{Value:=pair[B].Other}
Main():void={}
