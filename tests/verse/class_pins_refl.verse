# a type-equality witness: refl(t) is an eqw(t, t), so a cast through
# any eqw(a, b) is checked under the refinement b = a (#209)
eqw(a:type, b:type) := class<abstract>:
    Cast(X:a):b
refl(t:type) := class(eqw(t, t)):
    Cast<override>(X:t):t = X
Via(W:eqw(a, b), X:a where a:type, b:type):b = W.Cast(X)
Main():void =
    W:eqw(int, int) = refl(int){}
    Print("{Via(W, 41) + 1}")
    S:eqw(string, string) = refl(string){}
    Print(Via(S, "cast"))
