# expect: X.(a:)V: b has the field V of a and the one of i: openverse keeps one field of a name in a class
i := interface:
    V:int = 24
a := class:
    V:int = 12
b := class(a, i){}
Main():void = Print("{b{}.(a:)V}")
