# expect: requires convergence
Empty()<computes>:void = {}
holder(t:type) := class<computes> { Items:[]t = Empty() }
Main():void = Print("{holder(int){}.Items.Length}")
