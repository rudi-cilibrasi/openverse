# The value of a query of a logic is the empty value, false: `B?` succeeds
# when `B` is true, with the value false, and fails when `B` is false. Epic's
# Verse VM and Blueprint VM both print "equals false" for the three probes
# book-query-true-equals-false, book-query-and-value and book-query-or-value
# (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086), as the Book's tests
# expect (Operators/BoolQuery.versetest 3 and 4, LogicalAnd.versetest:29,
# Precedence.versetest 121 and 122); ch. 8's "succeeds with that value" is
# not followed.
QueryEqualsFalse()<computes><decides>:void = true? = false
AndEqualsFalse()<computes><decides>:void = (true? and true?) = false
OrEqualsFalse()<computes><decides>:void =
    X := true? or true
    X = false
OrRight()<computes><decides>:void =
    X := false? or true
    X = true
NotQueryQuery()<computes><decides>:void = not true??
Queried(B:logic)<computes><decides>:logic = B?

IsEven(N:int)<computes>:logic = logic{Mod[N, 2] = 0}

Show(B:logic):string = if (B?) then "true" else "false"

Main():void =
    if (QueryEqualsFalse[]) then Print("true? = false holds") else Print("true? = false fails")
    if (AndEqualsFalse[]) then Print("(true? and true?) = false holds") else Print("and fails")
    if (OrEqualsFalse[]) then Print("true? or true is false") else Print("or fails")
    if (OrRight[]) then Print("false? or true is true") else Print("or right fails")
    if (NotQueryQuery[]) then Print("not true?? holds") else Print("not true?? fails")
    # (a query still succeeds or fails as before: only its value changed)
    Flag:logic = true
    if (V := Flag?):
        Print("Flag? succeeded with {Show(V)}")
    if (Queried[false]) then Print("false? succeeded") else Print("false? failed")
    if (W := Queried[true]) then Print("Queried[true] gave {Show(W)}")
    L:logic = logic{Flag?}
    Print("logic of Flag? is {Show(L)}")
    O:?logic = option{Flag?}
    if (P := O?) then Print("option of Flag? holds {Show(P)}")
    var Count:int = 0
    for (I := 1..4, IsEven(I)?):
        set Count += 1
    Print("count {Count}")
