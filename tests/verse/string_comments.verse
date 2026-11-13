# A block comment inside a string is removed (Book of Verse ch. 1: "The
# compiler removes comments from strings"); \<\# is the text <#, and <#> is
# no block comment. The markers of block comments count in a # comment too:
# this one <# runs on
# to here #>, and the comment goes on to the end of its line.
Main():void =
    Print("abc<#def#>ghi")
    Print("a<# nested <# twice #> #>b")
    Print("\<\# kept \#\> <#> kept")
    Print("{"x<#y#>z"}")
