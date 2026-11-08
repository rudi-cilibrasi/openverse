# a generic override with a narrower (covariant) result type under the refinement (#198)
pair(a:type, b:type) := class:
    A:a
    B:b
    Me()<suspends>:pair(a, b) = Self
ipair(b:type) := class(pair(int, b)):
    Me<override>()<suspends>:ipair(b) =
        Sleep(0.1)
        Self
G(P:pair(a, b) where a:type, b:type)<suspends>:a =
    Q := P.Me()
    Q.A
Main()<suspends>:void =
    Print("{G(ipair(string){A := 1, B := "x"})}")
