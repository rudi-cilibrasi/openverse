# Control of join-named-tuple: ArrayAndNamedToString as a value of
# type{_(:string):string}, no join. Not a Book case. OpenVerse prints
#   value hello
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints value hello, as OpenVerse
# does.
ArrayAndNamedToString(X:string, ?Y:int = 1):string = X

Main():void =
    F:type{_(:string):string} = ArrayAndNamedToString
    Print("OVPROBE value {F("hello")}")
