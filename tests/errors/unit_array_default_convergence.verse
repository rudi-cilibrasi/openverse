# expect: the default of field 'Items' of holder calls Empty, which might not complete
Empty()<computes>:void = {}
holder(t:type) := class<computes> { Items:[]t = Empty() }
Main():void = Print("{holder(int){}.Items.Length}")
