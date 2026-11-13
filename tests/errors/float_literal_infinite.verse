# expect: 2:13: this float literal is out of range: it rounds to infinity
F():float = -1.7976931348623159e+308
Main():void = Print("{F()}")
