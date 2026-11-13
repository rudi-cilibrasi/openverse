# expect: 5:8: unexpected indentation
# The line's indentation, not the comment's width, places its first token.
Main():void =
    X := 1
        <#deeper#> Y := 2
