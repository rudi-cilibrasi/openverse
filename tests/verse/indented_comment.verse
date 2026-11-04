<#>
    An indented comment: the rest of the <#> line, then every following line
    indented more than it.

    Blank lines inside are part of it, and so is Main():void = Print("no").
        Deeper lines are too. <# and #> mean nothing here.

Main():void =
    Print("one")
    <#> this line,
        and the next two lines,
          are a comment
    Print("two")
    Print("three") <#> a <#> after code
        Print("hidden: more indented than the line of the <#>")
    if (1 > 0):
        Print("four")
    <#>
        Print("hidden too")
    else:
        Print("not printed")
    # `<#` opens a nested block comment only when the next character is not `>`
    <# outer <# inner #> still outer #>
    Print("five")
