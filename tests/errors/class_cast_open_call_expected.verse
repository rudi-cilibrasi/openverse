# expect: expected int, found u'
base(t:type):=class{Value:t}
pair(t:type,u:type):=class(base(t)){Other:u}
Echo(X:t,?Other:t=X where t:type):t=Other
Bad(B:base(int))<decides>:int=Echo(B.Value,?Other:=pair[B].Other)
Main():void={}
