# expect: ToDiagnostic of a value of the type parameter t is not supported yet: a value of type t is converted to any in a program that calls ToDiagnostic
# A generic function's value of a type parameter has no printer: its type
# is known only to the caller.
Erase(X:t where t:type):any = X
Main():void =
    Print(ToDiagnostic(Erase(1)).String)
