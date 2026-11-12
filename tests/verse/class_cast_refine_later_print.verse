# A refining cast after a clause that prints (#243): when the cast fails,
# the whole condition fails, and the Print is undone with it; when it
# succeeds, the Print stays and the branch is typed under the refinement.
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
Later(P:pair(a, b) where a:type, b:type)<transacts>:int =
    # (the cast comes after a Print)
    if (Print("x"), D := dup[P]) then D.C else 0
Main()<transacts>:void =
    Print("{Later(pair(int, int){A := 1, B := 2})}")
    Print("{Later(dup(int){A := 1, B := 2, C := 5})}")
