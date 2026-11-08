# expect: type parameter u of arr_box occurs only inside the type arguments arr_box gives its parent
box(t:type) := class:
    V:t
    Get():t = V
arr_box(u:type) := class(box([]u)):
    Get<override>():[]u = array{}
Main():void = Print("x")
