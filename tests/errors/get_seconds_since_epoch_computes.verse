# expect: GetSecondsSinceEpoch
# GetSecondsSinceEpoch is <reads> (#724): not in a <computes> function.
Now()<computes>:float = GetSecondsSinceEpoch()
Main():void = Print("{Now()}")
