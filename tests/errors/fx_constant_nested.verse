# expect: the constant W would hold an object with var fields or of a <unique> class
counter := class:
    var Count:int = 0
wrapper := class:
    C:counter
W:wrapper = wrapper{C := counter{}}
Main():void = Print("{W.C.Count}")
