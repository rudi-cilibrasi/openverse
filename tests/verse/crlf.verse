# CR LF line breaks: each CR LF is one line break.
<# a block comment
   over two lines #>
Twice(N:int):int =
    N + N

Main():void =
    X := Twice(21) # a line comment ends at CR LF
    if (X = 42):
        Print("X = {X}")
    else:
        Print("unreachable")
    <#> an indented comment
        Print("hidden")

    for (I := 1..2) {
        Print("I = {I}")
    }
    Print("last line")
