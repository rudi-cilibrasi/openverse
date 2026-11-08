# expect: branch in a generic function is not supported yet
G(X:t where t:type)<suspends>:t =
    branch:
        Sleep(1.0)
    X
Main()<suspends>:void = Print("{G(1)}")
