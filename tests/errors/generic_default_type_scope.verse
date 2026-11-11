# expect: unknown type 'u'
F(X:t,?Ys:[]t=block{ E:[]u=Concatenate(); E } where t:type):int = Ys.Length
Caller(X:u where u:type):int = F(X)
Main():void = Print("{Caller(7)}")
