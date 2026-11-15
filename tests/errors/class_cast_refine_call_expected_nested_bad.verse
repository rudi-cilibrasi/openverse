# expect: expected string, found int
# A cast after an unrelated error must not cause every wrapper to replay
# the failing subtree recursively (the original recovery did so exponentially).
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){Index:int=0}
Wrap(X:int):int=X
Need(X:string,?Index:int=0):int=Index
F(P:pair(a,b) where a:type,b:type)<decides>:int=Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Wrap(Need(1,?Index:=dup[P].Index)))))))))))))))))))))))))
Main():void={}
