# expect: Make constructs an object that has a var field or is <unique>, which its effects (<computes>) do not allow
token := class<unique>:
    N:int
Make()<computes>:token = token{N := 1}
Main():void = Print("{Make().N}")
