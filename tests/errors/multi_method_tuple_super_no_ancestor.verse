# expect: nothing above base implements 'Pick'
base(t:type) := class:
    Pick(X:t,Y:t):int = 1 | (super:)Pick((X,Y))
Main():void = for(N:=base(int){}.Pick(1,2)){Print("{N}")}