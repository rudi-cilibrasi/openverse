# expect: 12:7: this invocation calls a function (a value of type type{_(:int)<no_rollback>:int}) that has the 'no_rollback' effect, which a failure context does not allow
# (#515, --default-no-rollback) a function type without a heap specifier
# has no_rollback too, so a value of it cannot be called in a <transacts>
# <decides> function: UEFN 43.12 refuses both calls of the field with 3512
# (Book of Verse tests, ParametricTypes.versetest:222;
# tests/conformance/versevm/book/book-parametric-fn-field-tuple.verse)
my_type(t:type) := class{F:t->t}
F1(FLocal:t->t where t:type)<transacts>:my_type(t) = my_type(t){F := FLocal}
F2(X:int)<computes>:int = X + 1
F3()<transacts><decides>:void =
    C := F1(F2)
    C.F(0) = 1
Main():void =
    if (F3[]) then Print("succeeded") else Print("failed")
