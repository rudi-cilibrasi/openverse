# expect: 4:10: a char literal must be a printable ASCII character or an escape, not U+0009
# A raw tab between the quotes is an error: write '\t'.
Main():void =
    C := '	'
