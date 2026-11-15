# expect: expected int, found u'
base(t:type):=class{Value:t}
pair(t:type,u:type):=class(base(t)){Other:u}
Select(?Index:int=0):int=Index
Bad(B:base(int))<decides>:int=Select(?Index:=pair[B].Other)
Main():void={}
