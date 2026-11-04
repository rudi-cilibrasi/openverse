# expect: 4:9: a 0o char literal needs one or two hex digits
# 0o is followed by one or two hex digits: 0o41 is 'A'.
Main():void =
    C := 0o141
