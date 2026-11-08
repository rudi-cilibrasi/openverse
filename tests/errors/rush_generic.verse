# expect: rush in a generic function is not supported yet
W(X:t where t:type)<suspends>:t =
    rush:
        block:
            Sleep(1.0)
            X
        block:
            Sleep(2.0)
            X
Main()<suspends>:void = Print("{W(1)}")
