# expect: this case arm is never reached: an earlier arm has the same pattern
e := enum{A, B}
F(X:e):int =
    case (X):
        e.A => 1
        e.B => 2
        @ignore_unreachable e.A => 3
        e.A => 4
Main():void = {}
