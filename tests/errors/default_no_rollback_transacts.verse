# expect: 8:23: this invocation calls a function (F) that has the 'no_rollback' effect, which a body whose effects exclude it does not allow
# (#515, --default-no-rollback) a function without specifiers has Epic's
# default effect, no_rollback, which a <transacts> function cannot call:
# UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086) refuses this with error
# 3512 (Book of Verse tests, Effects.versetest:490;
# tests/conformance/versevm/book/book-default-effect-from-transacts.verse)
F():void = {}
G()<transacts>:void = F()
Main():void =
    G()
    Print("called")
