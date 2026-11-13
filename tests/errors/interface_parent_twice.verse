# expect: C names T twice among its parents: a parent is named once
T := interface {}
C := class(T, T) {}
Main():void = {}
