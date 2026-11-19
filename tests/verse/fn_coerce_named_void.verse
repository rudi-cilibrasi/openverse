# (#724) functions named where a type{_(:int):void} or a type{_(:int):int} is
# expected, a result discarded or an int parameter given to a void one: Epic's
# Verse compiler makes the wrapper for a name (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086:
# followup-coerce2/name-void-result), and the Book of Verse's tests have them
# valid on both VMs (Void.versetest 91, 104).
IntIdentity(X:int):int = X
VoidInput(:void):int = 19
Run(F(:int):void):void = F(1)
Main():void =
    Run(IntIdentity)
    F:int->void = IntIdentity
    F(0)
    G:int->int = VoidInput
    Print("{G(0)}")
