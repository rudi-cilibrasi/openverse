# expect: 'Self' is reserved: no definition can take it
c := class:
    F(Self:int):int = Self
Main():void = {}
