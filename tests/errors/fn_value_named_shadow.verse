# expect: 'F' has a named parameter ?F, which hides it in a call of its value
# Its value class could not call it by name: an OpenVerse restriction (#503)
F(?F:int = 3):int = F + 1
Main():void =
    G:type{_():int} = F
    Print("{G()}")
