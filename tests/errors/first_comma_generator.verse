# expect: 5:22: in first{…}, a comma joins its clauses into a tuple, and a generator inside a tuple is not supported yet
# In first{…}, commas join a tuple: (4,12) = first{X:=1..5, 3*X>10} (Book of
# Verse tests, FlowControl/first.versetest:206), a generator in a tuple.
Main()<decides>:void =
    V := first{X:=1..5, 3*X>10}
