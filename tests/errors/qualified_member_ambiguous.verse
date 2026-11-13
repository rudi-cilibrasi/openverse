# expect: 'X' is ambiguous here: the member (C:)X and a definition outside the class are both named so
X:int = 42
C := class:
    (C:)X:int = 1
    G():int = X
Main():void = {}
