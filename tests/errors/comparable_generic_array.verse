# expect: expected []comparable, found []t
# a value of a type parameter is boxed as an argument, a result, a local's
# value or an operand of = and <>; an array of them is not yet
F(X:t where t:subtype(comparable)):[]comparable = array{X}
Main():void = {}
