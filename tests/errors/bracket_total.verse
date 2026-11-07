# expect: Inc cannot fail: call it with Inc(…)
# The call syntax marks failure: F[…] only for a <decides> function.
Inc(X:int):int = X + 1

Main():void = Print("{Inc[1]}")
