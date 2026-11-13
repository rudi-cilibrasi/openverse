# expect: 4:13: a float literal is digits, a point and digits, then an optional exponent and suffix f64
# The suffix is f64, in lower case (the Book's tests refuse 1.23F64).
Main():void =
    X := 1.23F64
