# expect: '=' compares values of different types, tuple(t, t, t) and string, whose values in common Verse Core cannot compare
# A tuple of a type parameter and a string share values at one instance
# ('a', 'b', 'c') = "abc", Book of Verse Tests/Operators/CompareString
# 168-182) that Verse Core holds as a tuple and an array; generic code
# cannot convert the tuple: refused (docs/research/empty-values.md).
Same(A:tuple(t, t, t), B:string where t:subtype(comparable))<decides>:void = A = B
Main():void = {}
