# expect: 3:0: 'int' is the name of a built-in type
# Nor a field, which a method's bare use would read as the type.
c := class:
    int:int = 7
    Get():int = int
Main():void = Print("{c{}.Get()}")
