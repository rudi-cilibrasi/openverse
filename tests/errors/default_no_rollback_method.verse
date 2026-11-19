# expect: 9:20: this invocation calls a function (counter.Peek) that has the 'no_rollback' effect, which a body whose effects exclude it does not allow
# (#515, --default-no-rollback) a method without specifiers has it too
# (UEFN 43.12 refuses a <transacts> function calling a function without
# specifiers with error 3512: Effects.versetest:490)
counter := class:
    var N:int = 0
    Peek():int = N
    Bump()<transacts>:void =
        set N = Peek() + 1
Main():void =
    C := counter{}
    C.Bump()
