# branches (nested, and a rush inside) in a generic function, and in one (#254, from the review of #258)
# that calls itself at ever bigger types (polymorphic recursion)
G(X:t, Tag:string where t:type)<suspends>:t =
    defer:
        Print("{Tag} defer")
    branch:
        defer:
            Print("{Tag} A defer")
        Sleep(0.1)
        branch:
            defer:
                Print("{Tag} A.1 defer")
            Sleep(5.0)
        Y := rush:
            block:
                defer:
                    Print("{Tag} A.r1 defer")
                Sleep(5.0)
                1
            block:
                defer:
                    Print("{Tag} A.r2 defer")
                Sleep(5.0)
                2
        Sleep(5.0)
    branch:
        defer:
            Print("{Tag} B defer")
        Sleep(5.0)
    Sleep(0.5)
    X
Rec(X:t, N:int where t:type)<suspends>:int =
    defer:
        Print("Rec{N} defer")
    branch:
        defer:
            Print("Rec{N} A defer")
        Sleep(0.1)
        branch:
            defer:
                Print("Rec{N} A.1 defer")
            Sleep(5.0)
        Sleep(5.0)
    branch:
        defer:
            Print("Rec{N} B defer")
        Sleep(5.0)
    Sleep(0.2)
    if (N > 0) then Print("inner gave {Rec(array{X}, N - 1)}")
    Sleep(0.2)
    N
Main()<suspends>:void =
    Print("{G(5, "int")}")
    Print("{G("s", "string")}")
    Print("{Rec(1, 2)}")
