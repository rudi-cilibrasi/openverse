# expect: 3:25: cannot infer type parameter t of Len from the arguments of this call
Len(?Items:[]t = array{} where t:type):int = Items.Length
Main():void = Print("{Len()}")
