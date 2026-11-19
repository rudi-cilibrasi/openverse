# expect: 9:13: this invocation calls a function (Relay) that has the 'no_rollback' effect, which a body whose effects exclude it does not allow
# (#515) a method whose heap specifiers exclude no_rollback cannot call a
# function that signals: Relay has no specifiers, so the no_rollback effect
# (Book of Verse ch. 13; UEFN 43.12 refuses such a call with error 3512,
# tests/conformance/versevm/book/book-default-effect-from-transacts.verse)
Relay(E:event(int), N:int):void = E.Signal(N)
counter := class:
    Bump(E:event(int))<reads><writes><allocates>:void =
        Relay(E, 1)
Main():void =
    counter{}.Bump(event(int){})
