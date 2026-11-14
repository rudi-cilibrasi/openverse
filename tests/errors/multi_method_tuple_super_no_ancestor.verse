# expect: nothing above base implements 'Pick'
picks(t:type) := interface:
    Pick(X:t,Y:t):int
base(t:type) := class(picks(t)):
    Pick<override>(X:t,Y:t):int = 1 | (super:)Pick((X,Y))
Main():void = for(N:=base(int){}.Pick(1,2)){Print("{N}")}