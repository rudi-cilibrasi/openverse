node(t:type) := interface:
    Down(N:int)<computes>:int
fixed := class(node(int)):
    Down<override>(N:int)<computes>:int = if (N > 0) then (N | Down(N - 1)) else 0
Main():void = for (V:=fixed{}.Down(3)) { Print("{V}") }
