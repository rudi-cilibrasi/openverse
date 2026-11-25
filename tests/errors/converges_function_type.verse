# expect: <converges> is unsupported on a function with a body
# <converges> in a function type stays refused (#724 admits it on a method
# without a body only).
Count():int = 1
Main():void =
    F:type{_()<converges>:int} = Count
    Print("{F()}")
