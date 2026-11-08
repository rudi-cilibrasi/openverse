# expect: a <suspends> method cannot be dispatched to class int_box
box(t:type) := class:
    V:t
    Get()<suspends>:t = V
int_box := class(box(int)):
    Get<override>()<suspends>:int = V + 1
G(B:box(t) where t:type)<suspends>:t = B.Get()
Main()<suspends>:void = Print("{G(int_box{V := 1})}")
