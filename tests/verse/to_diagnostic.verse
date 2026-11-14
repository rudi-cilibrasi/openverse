# ToDiagnostic (the Book of Verse's API reference: "Accepts any value at
# all"), its value passed through a parameter of type any, as the Book's
# tests do (Tests/Intrinsics/ToDiagnostic.versetest), whose formats these
# are: ints in decimal, rationals reduced, chars quoted or as 0oXX, char32s
# as 0uX, strings quoted and escaped, options, arrays, tuples and maps, an
# object's or a struct's fields, an enum's value, and a diagnosable
# object's own diagnostic.
Show(Value:any)<reads>:void = Print(ToDiagnostic(Value).String)

my_class := class:
    X:int
my_parametric_class(t:type) := class:
    X:t
letters := enum{A, B}
pair := struct:
    X:int
    Y:string
named := class(diagnosable):
    Name:string
    GetDiagnostic<override>()<reads>:diagnostic = diagnostic{String := Name}
base := class:
    A:int = 1
derived := class(base):
    B:logic = true
node := class:
    Value:int
    Next:?node = false
Scale(X:int, Y:float):void = {}
counter := class:
    Count(X:int):void = {}
M := module:
    point<public> := class:
        X<public>:int = 3

Main():void =
    Show(false)
    Show(true)
    Show(0)
    Show(-1000)
    Show(9223372036854775807)
    if (R1 := 2 / 4, R2 := -2 / -4, R3 := 10 / 5, R4 := -1 / 1645333507):
        Show(R1)
        Show(R2)
        Show(R3)
        Show(R4)
    Show('a')
    Show('\t')
    Show('\#')
    Show(0o00)
    Show(0o7f)
    Show(0u9)
    Show(0u1f600)
    Show("")
    Show("abc{0o00}def")
    Show("\t\n\r\"\#\&\'\<\>\\\{\}\~")
    Show("{0o08}{0o09}{0o0a}{0o0b}")
    Show("Smiley face: 😀, rocket: 🚀")
    Show("{0odf}{0obf}{0odf}{0o00}")
    Show("{0of4}{0o8f}{0obf}{0obf}{0off}")
    Show(option{1})
    Show(option{"abc"})
    O:?int = false
    Show(O)
    Show(array{1})
    Show(array{1, 2, 3})
    Show(array{array{1, 2}, array{3, 4}})
    E:[]int = array{}
    Show(E)
    Show((1, 2, 3))
    Show(((1, 2), (3, 4)))
    Show(map{(0, 0) => 0, (1, 1) => 1})
    Show(map{"a" => true})
    Show(my_class{X := 10})
    Show(my_parametric_class(int){X := 0})
    Show(letters.B)
    Show(pair{X := 1, Y := "one"})
    Show(named{Name := "Object1"})
    Show(ToDiagnostic("test"))
    B:base = derived{}
    Show(B)
    Show(base{A := 2})
    Show(node{Value := 1, Next := option{node{Value := 2}}})
    Values:[]any = array{1, "two", option{'3'}}
    for (V : Values):
        Show(V)
    Show(Values)
    Show(())
    Show(Scale)
    Show(ToDiagnostic)
    Show(counter{}.Count)
    Show(M.point{})
