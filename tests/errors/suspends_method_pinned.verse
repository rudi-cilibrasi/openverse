# expect: a <suspends> method with type parameters (its class's or its own) cannot be dispatched to class ipair, which fixes type arguments of pair, yet
pair(a:type, b:type) := class:
    A:a
    B:b
    First()<suspends>:a = A
ipair(b:type) := class(pair(int, b)):
    First<override>()<suspends>:int = A + 1
G(P:pair(a, b) where a:type, b:type)<suspends>:a = P.First()
Main()<suspends>:void = Print("{G(ipair(string){A := 1, B := "x"})}")
