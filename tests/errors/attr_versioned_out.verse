# expect: unknown function 'F'
@available{MinUploadedAtFNVersion := 4294967295}
F():int = 1
Main():void = Print("{F()}")
