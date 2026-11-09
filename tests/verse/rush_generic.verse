# formerly refused; generic functions with task roots, compiled once (#174, #244)
W(X:t where t:type)<suspends>:t =
    rush:
        block:
            Sleep(1.0)
            X
        block:
            Sleep(2.0)
            X
Main()<suspends>:void = Print("{W(1)}")
