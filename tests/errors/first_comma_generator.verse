# expect: 6:31: in first{…}, a comma joins its clauses into a tuple, and a generator inside a tuple is supported only when every separator is a comma and no generator has an index
# In first{…}, commas join a tuple: (4,12) = first{X:=1..5, 3*X>10} (Book of
# Verse tests, FlowControl/first.versetest:206; tests/verse/first_comma_tuple.verse). With an
# indexed generator among the clauses the tuple is not made, and the comma is refused.
Main()<decides>:void =
    V := first{I->X:array{7, 8}, X > 7}
