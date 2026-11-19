# expect: 7:13: this invocation calls a function (Count) that has the 'no_rollback' effect, which a failure context does not allow
# (#515, --default-no-rollback) nor a failure context: an if's condition
# (UEFN 43.12 refuses a Signal there, which has no_rollback, with 3512;
# tests/conformance/versevm/signal-direct.verse)
Count():int = 3
Main():void =
    if (Count() > 2):
        Print("big")
