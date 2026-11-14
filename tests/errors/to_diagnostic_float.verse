# expect: ToDiagnostic of a float (the shortest decimal that reads back is a Verse Core primitive not written yet) is not supported yet: a value of type float is converted to any in a program that calls ToDiagnostic
# In a program that calls ToDiagnostic, a value converted to any keeps what
# it needs to print itself; a float's printer, the shortest decimal that
# reads back (the Book's tests: 1.5, 1e+100), is not written yet.
Main():void =
    Print(ToDiagnostic(1.5).String)
