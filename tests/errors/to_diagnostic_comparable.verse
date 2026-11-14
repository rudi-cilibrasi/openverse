# expect: ToDiagnostic of a comparable (the type of its value is in its box, which no Verse code reads) is not supported yet: a value of type comparable is converted to any in a program that calls ToDiagnostic
# A comparable is a box whose type no Verse code reads, so it has no printer.
Main():void =
    C:comparable = 1
    Print(ToDiagnostic(C).String)
