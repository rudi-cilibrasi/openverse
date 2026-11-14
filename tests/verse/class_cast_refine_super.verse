# A refining cast's branch in a method that calls (super:) (#243): the implementation the method's class inherits, called directly with Self
# ((super:)Name only in an override of Name, the Book's rule: the method is an overload of Name)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
base := class:
    Name():string = "base"
    Name(P:pair(a, b), X:a where a:type, b:type):b = P.B
holder := class(base):
    Name<override>():string = "holder"
    Name<override>(P:pair(a, b), X:a where a:type, b:type):b =
        if (D := dup[P]):
            Print((super:)Name())
            X
        else:
            P.B
Main():void = Print("{holder{}.Name(dup(int){A := 1, B := 2}, 3)}")
