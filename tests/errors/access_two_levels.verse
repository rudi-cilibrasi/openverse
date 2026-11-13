# expect: a method has two access specifiers, <public> and <internal>: a definition has one access level
counter := class:
    Get<public><internal>():int = 0
Main():void = {}
