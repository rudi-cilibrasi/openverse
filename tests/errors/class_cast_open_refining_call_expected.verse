# expect: expected b, found u'
# Discovering the later cast can refine a=b and open u together; the
# expected result must still reject a value of that unrelated opened u.
pair(a:type,b:type):=class:
    A:a
    B:b
openDup(t:type,u:type):=class(pair(t,t)){Other:u}
Echo(X:t,?Other:t=X where t:type):t=Other
Bad(P:pair(a,b) where a:type,b:type)<decides>:b=Echo(P.A,?Other:=openDup[P].Other)
Main():void={}
