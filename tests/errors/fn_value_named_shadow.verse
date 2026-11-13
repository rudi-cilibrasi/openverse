# expect: the named parameter '?F' of F has the name of the function F (5:0): Verse does not allow shadowing
# (Book of Verse ch. 10: a parameter cannot take an enclosing definition's
# name, and a named one cannot be qualified; before, its value class could
# not call it by name, an OpenVerse restriction, #503)
F(?F:int = 3):int = F + 1
Main():void =
    G:type{_():int} = F
    Print("{G()}")
