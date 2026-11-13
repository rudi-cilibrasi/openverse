# expect: 4:19: cannot mix ',' and ';' separators
# The Book's MixedArray (ch. 1): commas or semicolons, not both.
Main():void =
    A := array{1, 2; 3}
