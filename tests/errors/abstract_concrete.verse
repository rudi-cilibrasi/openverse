# expect: shape cannot be both <abstract> and <concrete>
shape := class<abstract><concrete>:
    Sides:int = 0
Main():void = {}
