# comparable as a type (Book of Verse ch. 11, "Comparable and Equality" and
# "Dynamic Comparable Values"): every value of a comparable type converts to
# it, and = with a comparable holds exactly when both values have the same
# type and are equal (an int is never a float, an enum's value never another
# enum's or an int), while what Verse identifies stays one value (the empty
# value, a tuple and the array of its elements, an int and the rational it
# is, a struct at two instances). Each result is y (holds) or n (fails).
letters := enum{A, B, C}
numbers := enum{One, Two, Three}
p := struct:
    C:int
q := struct:
    C:int
s := struct {}
pc(t:type) := struct{X:t}
holder := struct:
    V:comparable
AsComparable(X:comparable):comparable = X
Same(A:comparable, B:comparable)<decides>:void = A = B
Show(B:logic):string = if (B?) then "y" else "n"
Main():void =
    # the Book's own examples
    Print("{Show(logic{comparable(15) = comparable(15)})} {Show(logic{comparable("Hello") = "Hello"})}")
    Print("{Show(logic{array{AsComparable(1)} = array{1}})} {Show(logic{array{AsComparable(1)} <> array{2}})} {Show(logic{array{1} = array{AsComparable(1)}})}")
    # different types: never equal
    Print("{Show(logic{Same[0, 0.0]})} {Show(logic{Same[letters.A, numbers.One]})} {Show(logic{Same[letters.A, 0]})} {Show(logic{Same[0u41, 65]})} {Show(logic{Same[letters.B, letters.B]})} {Show(logic{Same[letters.B, letters.C]})}")
    Print("{Show(logic{Same[p{C := 1}, q{C := 1}]})} {Show(logic{Same[p{C := 1}, p{C := 1}]})} {Show(logic{Same[p{C := 1}, 1]})} {Show(logic{Same[p{C := 1}, array{1}]})}")
    Print("{Show(logic{Same[map{1 => 2}, array{(1, 2)}]})} {Show(logic{Same[map{1 => 2}, map{1 => 2}]})} {Show(logic{Same['a', 97]})} {Show(logic{Same[0u61, 'a']})}")
    # what Verse identifies: one value
    Print("{Show(logic{Same[(1, 2, 3), array{1, 2, 3}]})} {Show(logic{Same[('a', 'b'), "ab"]})} {Show(logic{Same[(97, 98), "ab"]})}")
    if (R := 4 / 2, H := 1 / 2):
        Print("{Show(logic{Same[R, 2]})} {Show(logic{Same[H, (1, 2)]})} {Show(logic{Same[H, H]})} {Show(logic{Same[array{R}, array{2}]})}")
    A:[]int = array{}
    S:string = ""
    E:[int]int = map{}
    O:?int = false
    U:tuple() = ()
    Print("{Show(logic{Same[false, A]})} {Show(logic{Same[A, S]})} {Show(logic{Same[S, E]})} {Show(logic{Same[O, U]})} {Show(logic{Same[s{}, false]})} {Show(logic{Same[s{}, s{}]})} {Show(logic{Same[option{false}, option{()}]})}")
    Print("{Show(logic{Same[pc(int){X := 0}, pc(float){X := 0.0}]})} {Show(logic{Same[pc([]int){X := array{1, 2}}, pc(tuple(int, int)){X := (1, 2)}]})}")
    # a map keyed by comparable values
    M:[comparable]string = map{0 => "int", 0.0 => "float", letters.A => "A", "0" => "string", (1, 2) => "pair"}
    Print("{M.Length}")
    if (V := M[0]) then Print(V) else Print("none")
    if (V := M[0.0]) then Print(V) else Print("none")
    if (V := M[letters.A]) then Print(V) else Print("none")
    if (V := M[numbers.One]) then Print(V) else Print("none")
    if (V := M[array{1, 2}]) then Print(V) else Print("none")
    if (V := M[comparable("0")]) then Print(V) else Print("none")
    # an array of values of several types: its element type is comparable
    Mixed := array{1, "two", 3.0}
    Print("{Show(logic{Mixed[1] = "two"})} {Show(logic{Mixed[2] = 3})} {Mixed.Length}")
    if (I := Mixed.Find["two"]) then Print("{I}") else Print("none")
    if (I := Mixed.Find[1.0]) then Print("{I}") else Print("none")
    # a variable, a field, an option
    var X:comparable = 1
    set X = "a"
    Print("{Show(logic{X = "a"})} {Show(logic{X = 1})}")
    H := holder{V := letters.C}
    Print("{Show(logic{H.V = letters.C})} {Show(logic{H.V = 2})} {Show(logic{Same[holder{V := 1}, holder{V := 1}]})} {Show(logic{Same[holder{V := 1}, holder{V := 1.0}]})}")
    OC:?comparable = option{1}
    Print("{Show(logic{OC = option{1}})} {Show(logic{OC = option{1.0}})}")
    # an array of char32 as an array of comparable: each one boxed
    C32:[]char32 = array{0u41, 0u42}
    var CA:[]comparable = C32
    Print("{Show(logic{CA = array{0u41, 0u42}})} {Show(logic{CA = array{65, 66}})}")
    # the join of an int and a string is comparable
    J := if (X = "a") then 1 else "b"
    Print("{Show(logic{J = 1})} {Show(logic{J = "b"})}")
    Y:any = comparable(1)
    # values Verse Core holds differently that Verse may find equal: boxed
    # (Tests/Operators/CompareArray, a char32 is no int)
    T1:[]tuple(int, []int) = array{(1, array{})}
    T2:[]tuple(int, []char32) = array{(1, array{})}
    T3:[]tuple(int, []char32) = array{(1, array{0u1})}
    T4:[]tuple(int, []int) = array{(1, array{1})}
    Print("{Show(logic{T1 = T2})} {Show(logic{T3 = T4})} {Show(logic{T4 = T4})}")
