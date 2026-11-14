# An abstract class's qualified <suspends> implementation of an interface's
# method ((top:)Get), reached by a dispatch to a class that fixes its
# class's type argument to a compound of its own: its frame is opened too,
# found by the lowering (#394; an interface overrides nothing, the Book's
# tests, so job is a class)
top(a:type, b:type) := interface:
    Get(X:b)<suspends>:a
job(t:type) := class<abstract>(top(t, int)):
    Make():t
    (top:)Get<override>(X:int)<suspends>:t =
        Sleep(0.01)
        Make()
c1(s:type) := class(job(s)):
    V:s
    Make<override>():s = V
c3(u:type) := class(c1(tuple(char, u))):
    Make<override>():tuple(char, u) = V
G(B:top(a, b), Y:b where a:type, b:type)<suspends>:a = B.Get(Y)
Main()<suspends>:void =
    Y := G(c1(int){V := 3}, 2)
    Print("{Y}")
    X := G(c3(int){V := ('a', 5)}, 1)
    Print("{X(0)} {X(1)}")
