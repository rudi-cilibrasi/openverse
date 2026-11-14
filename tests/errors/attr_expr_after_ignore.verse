# expect: 5:29: @deprecated is on an expression or a local definition
# An expression takes @ignore_unreachable and no other attribute: the
# refusal names the other, where it is written.
Main():void =
    X := @ignore_unreachable @deprecated 1
    Print("{X}")
