# A block comment before the first token of a line does not indent it: the
# token has the line's indentation as its column (Book of Verse tests,
# Roundtrip/Comments: `<#C0#>f<#C1#>(<#C2#>)<#C3#>:<#C4#>void<#C5#> = <#C6#>3`).
<#C0#>f<#C1#>(<#C2#>)<#C3#>:<#C4#>int<#C5#> = <#C6#>3<#C7#>
Main():void =
    <#a#> X := f()
    <#b#>Print("{X}")
