# expect: arr_box has type parameters that box does not have, so it cannot override Get
box(t:type) := class:
    V:t
    Get():t = V
arr_box(u:type) := class(box([]u)):
    Get<override>():[]u = array{}
Main():void = Print("x")
