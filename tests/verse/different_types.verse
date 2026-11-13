# = and <> compare values of any two comparable types (Book of Verse ch. 4,
# "Comparisons between different types still compile, but they always
# fail"): values of different types are different values, but for the one
# empty value (ch. 2), a tuple, which is the array of its elements, and an
# int, which is a rational. Verse Core holds a char32, an enum and an int
# alike, and two structs of one layout, so these are never equal. Each
# result is y (holds) or n (fails).
p := struct:
    C:int
q := struct:
    C:int
s := struct {}
e := enum{A, B}
f := enum{A, B}
pc(t:type) := struct{X:t}
Show(B:logic):string = if (B?) then "y" else "n"
Main():void =
    Print("{Show(logic{0u41 = 65})} {Show(logic{0u41 <> 65})} {Show(logic{0 = 0.0})} {Show(logic{0 <> 0.0})}")
    Print("{Show(logic{array{1} = array{1.0}})} {Show(logic{array{1} <> array{1.0}})}")
    A:[]int = array{}
    F:[]float = array{}
    Print("{Show(logic{A = F})} {Show(logic{A <> F})}")
    Print("{Show(logic{p{C := 1} = q{C := 1}})} {Show(logic{p{C := 1} <> q{C := 1}})}")
    X:?char32 = option{0u41}
    Y:?int = option{65}
    N:?char32 = false
    M:?int = false
    Print("{Show(logic{X = Y})} {Show(logic{X <> Y})} {Show(logic{N = M})} {Show(logic{N <> M})} {Show(logic{X = M})}")
    T:tuple(char32, int) = (0u41, 1)
    U:tuple(int, int) = (65, 1)
    Print("{Show(logic{T = U})} {Show(logic{T <> U})}")
    Print("{Show(logic{e.A = 0})} {Show(logic{e.A = f.A})} {Show(logic{e.A <> f.A})}")
    Print("{Show(logic{(97, 98) <> "ab"})} {Show(logic{('a', 'b') = "ab"})} {Show(logic{"" <> array{0}})}")
    Print("{Show(logic{array{(1, 2)} = map{1 => 2}})} {Show(logic{array{(1, 2)} <> map{1 => 2}})}")
    if (R := 2 / 2) then Print("{Show(logic{array{1} = array{R}})} {Show(logic{R = 1.0})} {Show(logic{0 = false})} {Show(logic{R = (1, 1)})}")
    Print("{Show(logic{s{} = ()})} {Show(logic{s{} <> ()})} {Show(logic{true = option{0}})}")
    Print("{Show(logic{pc(int){X := 0} = pc(float){X := 0.0}})} {Show(logic{pc(int){X := 0} <> pc(float){X := 0.0}})}")
    # (one struct at two instances: its fields compared as values, a tuple as
    # the array of its elements, an int as a rational; Book of Verse
    # Tests/Operators/CompareStruct.versetest 40 to 45)
    Print("{Show(logic{pc([]int){X := array{1, 2}} = pc(tuple(int, int)){X := (1, 2)}})} {Show(logic{pc([]int){X := array{1, 2}} = pc(tuple(int, int)){X := (2, 3)}})}")
    if (R := 2 / 2) then Print("{Show(logic{pc(int){X := 1} = pc(rational){X := R}})} {Show(logic{pc(int){X := 2} <> pc(rational){X := R}})}")
    if (0u41 = 65 = 65) then Print("chain y") else Print("chain n")
