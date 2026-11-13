# expect: X.(c:)F: c does not introduce F, it overrides it: a qualifier names where the method is defined, (i:)
i := interface:
    F():int
c := class(i):
    F<override>():int = 1
Main():void = Print("{c{}.(c:)F()}")
