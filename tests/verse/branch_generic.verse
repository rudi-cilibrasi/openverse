# formerly refused; generic functions with task roots are specialised (#174)
G(X:t where t:type)<suspends>:t =
    branch:
        Sleep(1.0)
    X
Main()<suspends>:void = Print("{G(1)}")
