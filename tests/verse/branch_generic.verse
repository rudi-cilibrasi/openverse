# formerly refused; generic functions with task roots, compiled once (#174, #244)
G(X:t where t:type)<suspends>:t =
    branch:
        Sleep(1.0)
    X
Main()<suspends>:void = Print("{G(1)}")
