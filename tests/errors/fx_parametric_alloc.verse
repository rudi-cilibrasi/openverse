# expect: Make constructs an object that has a var field or is <unique>, which its effects (<computes>) do not allow
cell(t:type) := class<allocates>:
    var Value:t
Make()<computes>:cell(int) = cell(int){Value := 1}
Main():void = Print("{Make().Value}")
