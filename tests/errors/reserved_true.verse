# expect: 'true' is reserved: no definition can take it
m := module:
    (m:)true := enum{a}
Main():void = {}
