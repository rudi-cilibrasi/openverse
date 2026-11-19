# expect: grandchild inherits <concrete> from base, so its field 'Late' needs a default
# (UEFN 43.12: error 3519) through a class between them as well
base := class<concrete>:
    A:int = 1
child := class(base):
    B:int = 2
grandchild := class(child):
    Late:int
Main():void =
    Print("compiled")
