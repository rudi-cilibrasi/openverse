# expect: '=' compares values of different types, ?logic and ?void, whose values in common Verse Core cannot compare
# option{false} and option{()} are one value (Book of Verse ch. 2: the empty
# value inside an option), which Verse Core holds as two: refused until its
# equality relates them (docs/research/empty-values.md, Part 2)
Main():void =
    if (option{false} = option{()}) then Print("equal")
