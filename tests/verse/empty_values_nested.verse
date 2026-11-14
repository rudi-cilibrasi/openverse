# The empty value inside arrays, options, tuples, maps and structs, and
# through generic code: false, (), "", array{}, map{} and an empty option are
# one value (Book of Verse ch. 2), whatever type holds it and at whatever
# depth, so Verse Core's equality relates them (Value.veq). y: the
# comparison holds, n: it fails.
p(t:type) := struct{X:t}
IsFalse(X:t where t:subtype(comparable))<decides>:void = X = false
IsEmptyString(X:t where t:subtype(comparable))<decides>:void = X = ""
Same(X:t, Y:t where t:subtype(comparable))<decides>:void = X = Y
Show(B:logic):string = if (B?) then "y" else "n"
Main():void =
    LL:[]logic = array{false, false}
    SS:[]string = array{"", ""}
    OA:?[]int = option{array{}}
    O:?int = false
    # inside an array, an option, a tuple, one struct at two instances
    Print("{Show(logic{array{false} = array{()}})} {Show(logic{array{false} <> array{()}})} {Show(logic{LL = SS})}")
    Print("{Show(logic{option{false} = option{()}})} {Show(logic{OA = option{""}})} {Show(logic{option{false} = option{true}})}")
    Print("{Show(logic{(false, 1) = ((), 1)})} {Show(logic{(false, 1) = ((), 2)})} {Show(logic{(false, "") = ((), O)})}")
    Print("{Show(logic{p(logic){X := false} = p(void){X := ()}})} {Show(logic{p(logic){X := true} = p(void){X := ()}})}")
    Print("{Show(logic{p([]int){X := array{1, 2}} = p(tuple(int, int)){X := (1, 2)}})} {Show(logic{(1, 2) = array{(), ()}})}")
    # a type parameter at each type: X = false, X = ""
    A:[]int = array{}
    S:string = ""
    L:logic = false
    B:[]int = array{1}
    Print("{Show(logic{IsFalse[A]})} {Show(logic{IsFalse[O]})} {Show(logic{IsFalse[S]})} {Show(logic{IsFalse[L]})} {Show(logic{IsFalse[B]})} {Show(logic{IsFalse[0]})} {Show(logic{IsFalse[()]})}")
    Print("{Show(logic{IsEmptyString[A]})} {Show(logic{IsEmptyString[O]})} {Show(logic{IsEmptyString[L]})} {Show(logic{IsEmptyString[B]})}")
    # map keys and searched values holding the empty value (an array is no
    # map key, Book of Verse ch. 3: an option is)
    M:[?int]int = map{false => 1, option{0} => 2}
    if (V := M[false]) then Print("{V}")
    Xs:[][]logic = array{array{false}, array{true}, array{false}}
    Print("{for (Z : Xs, Same[Z, array{false}]) {Z}.Length}")
    Ys:[]tuple(?int, string) = array{(false, ""), (option{1}, ""), (false, "a")}
    Print("{for (Z : Ys, Same[Z, (false, "")]) {Z}.Length}")
