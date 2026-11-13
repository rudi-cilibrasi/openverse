# expect: 8:11: cannot mix ',' and ';' separators
# A construction's fields are separated by commas, or by new lines, not both.
abc := class:
    A:int := 1
    B:int := 2
F():abc = abc{
    A := 10
    B := 20,
}
Main():void = {}
