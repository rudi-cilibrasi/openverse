# expect: X.(b:)V: b does not declare the field V itself
a := class:
    V:int = 12
b := class(a){}
Main():void = Print("{b{}.(b:)V}")
