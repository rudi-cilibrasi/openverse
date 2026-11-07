# expect: an operand of '=' must be comparable, and t is not: declare t:subtype(comparable)
# = needs comparable operands; an unconstrained type parameter is not.
Same(A:t, B:t where t:type)<decides>:t = A = B

Main():void = Print("never called")
