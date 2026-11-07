# expect: cannot infer type parameter t of Empty
Empty(N:int where t:type):[]t = array{}

Main():void = Print("{Empty(3).Length}")
