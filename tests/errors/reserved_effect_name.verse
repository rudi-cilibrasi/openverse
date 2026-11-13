# expect: 'suspends' is reserved: no definition can take it
m := module:
    (m:)suspends := class {}
Main():void = {}
