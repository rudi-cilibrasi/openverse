# Control of join-named-tuple: ArrayAndNamedToString as a value of
# type{_(:string):string}, no join. Not a Book case. OpenVerse prints
#   value hello
ArrayAndNamedToString(X:string, ?Y:int = 1):string = X

Main():void =
    F:type{_(:string):string} = ArrayAndNamedToString
    Print("OVPROBE value {F("hello")}")
