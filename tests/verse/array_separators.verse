# An array's elements in braces are separated by commas, or by `;` and new
# lines, not both (Book of Verse ch. 1, "Semicolons vs Commas":
# `SemiArray := array{1; 2; 3}`).
Main():void =
    A := array{1; 2; 3}
    B := array{
        4
        5
    }
    Print("{A.Length} {B.Length}")
