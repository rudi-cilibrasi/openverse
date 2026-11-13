# Generic code compares and boxes values of its type parameters (Book of
# Verse ch. 11; Tests/Comparable.versetest 3 to 8, Tests/Operators/
# CompareString.versetest 167 to 182): a type parameter declared
# subtype(comparable) carries its box as the evidence of that bound, so a
# value of it is compared with a value of another type, or converted to
# comparable, as its box. Each result is y (holds) or n (fails).
letters := enum{A, B, C}
numbers := enum{One, Two, Three}
s := struct {}
p := struct:
    C:int
Equal(X:t, Y:comparable where t:subtype(comparable))<computes><decides>:t = X = Y
NotEqual(X:t, Y:comparable where t:subtype(comparable))<computes><decides>:t = X <> Y
Same(X:t, Y:u where t:subtype(comparable), u:subtype(comparable))<decides>:void = X = Y
Outer(X:t, Y:u where t:subtype(comparable), u:subtype(comparable))<decides>:void = Same[X, Y]
InArrays(X:t, Y:u where t:subtype(comparable), u:subtype(comparable))<decides>:void = array{X} = array{Y}
IsFalse(X:t where t:subtype(comparable))<decides>:void = X = false
TupleIsString(A:tuple(t, t, t), B:string where t:subtype(comparable))<decides>:void = A = B
AsComparable(X:comparable):comparable = X
Box(X:t where t:subtype(comparable)):comparable = AsComparable(X)
SameT(X:t, Y:t where t:subtype(comparable))<decides>:void = X = Y
BoxResult(X:t where t:subtype(comparable)):comparable = X
BoxAll(X:t, Y:u where t:subtype(comparable), u:subtype(comparable)):[]comparable =
    A:comparable = X
    B:comparable = BoxResult(Y)
    array{A, B}
Show(B:logic):string = if (B?) then "y" else "n"
Main():void =
    Print("{Show(logic{Equal[1, 1]})} {Show(logic{Equal['a', 'a']})} {Show(logic{Equal[array{AsComparable(1)}, array{1}]})} {Show(logic{Equal[array{1, 2, 3}, (1, 2, 3)]})} {Show(logic{Equal[(4, 5, 6), array{4, 5, 3}]})}")
    Print("{Show(logic{Equal[letters.A, letters.A]})} {Show(logic{Equal[letters.A, numbers.One]})} {Show(logic{Equal[letters.A, 0]})} {Show(logic{NotEqual[1, 2]})} {Show(logic{NotEqual[1, 1]})}")
    Print("{Show(logic{Same[0, 0.0]})} {Show(logic{Same[letters.B, letters.B]})} {Show(logic{Same[p{C := 1}, 1]})} {Show(logic{Same[0u41, 65]})} {Show(logic{Same[(1, 2), array{1, 2}]})}")
    Print("{Show(logic{Outer[1, 1]})} {Show(logic{Outer[1, 1.0]})} {Show(logic{InArrays[1, 1]})} {Show(logic{InArrays[letters.A, numbers.One]})} {Show(logic{InArrays[(1, 2), array{1, 2}]})}")
    A:[]int = array{}
    L:logic = false
    Print("{Show(logic{IsFalse[s{}]})} {Show(logic{IsFalse[A]})} {Show(logic{IsFalse[L]})} {Show(logic{IsFalse[0]})}")
    Print("{Show(logic{TupleIsString[('a', 'b', 'c'), "abc"]})} {Show(logic{TupleIsString[(97, 98, 99), "abc"]})} {Show(logic{TupleIsString[(0u61, 0u62, 0u63), "abc"]})}")
    Print("{Show(logic{Box(letters.A) = Box(numbers.One)})} {Show(logic{Box(1) = comparable(1)})}")
    R:rational = 4 / 2 or 0
    Print("{Show(logic{Box(R) = 2})} {Show(logic{Box(R) = 2.0})}")
    Print("{Show(logic{SameT[s{}, s{}]})} {Show(logic{SameT[letters.C, letters.C]})}")
    Print("{Show(logic{BoxResult(letters.A) = BoxResult(0)})} {Show(logic{BoxAll(letters.B, 1) = array{letters.B, 1}})} {Show(logic{BoxAll(letters.B, 1) = array{numbers.Two, 1}})}")
