# A construction may give its fields as an indented block after `:` (an
# archetype block, Book of Verse tests: `X := class1:` and `Property1 := 0`
# indented), also after type arguments or a qualifier; in braces they are
# separated by commas, or by `;` and new lines, not both.
abc := class:
    A:int := 1
    B:int := 2
    C:int := 3
pair(t:type) := struct:
    First:t
    Second:t
M := module:
    pt<public> := struct:
        X<public>:int = 0
Main():void =
    X := abc{
        A := 10
        B := 20
    }
    Y := abc:
        C := 30
        A := 5; B := 6
    P := pair(int):
        First := 1
        Second := 2
    Q := (M:)pt:
        X := 9
    Print("{X.A} {X.B} {X.C} {Y.A} {Y.B} {Y.C} {P.Second} {Q.X}")
