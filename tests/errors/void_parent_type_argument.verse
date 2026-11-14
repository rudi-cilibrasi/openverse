# expect: expected tuple(), found int
# (Book of Verse ch. 2: void given as a parent's type argument is true too,
# so the inherited field X:t holds the empty value alone)
box(t:type) := class:
    X:t
c := class(box(void)):
    Y:int = 0
Main():void =
    C := c{X := 1}
