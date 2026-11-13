# expect: 6:4: unknown identifier 'Probe'
# The `;` ends the class's field; Main is a definition of its own, not a method.
c := class:
    A:int = 0;
Main():void =
    Probe
