# expect: thing is <concrete>, so its field 'Field' needs a default
# (an interface's field too: C{} constructs a <concrete> class)
has_field := interface:
    Field:int
thing := class<concrete>(has_field):
    Other:int = 1
Main():void = {}
