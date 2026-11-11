# An inherited interface default keeps its lexical super, including copies.
iroot(a:type) := interface:
    Get():a
    Read()<transacts>:a = Get()
    Values()<transacts>:a = Get()|Get()
imid(b:type,c:type) := interface(iroot(b)):
    Values<override>()<transacts>:b = (super:)Read()|Get()
holder(x:type,y:type) := class(imid(x,y)):
    Value:x
    Extra:y
    Get<override>():x = Value
    Read<override>()<transacts>:x =
        Print("wrong dispatch")
        Value
All(H:holder(t,u) where t:type,u:type):[]t = for(V:=H.Values()): V
Main():void = for(V:All(holder(string,int){Value:="s",Extra:=7})): Print("{V}")
