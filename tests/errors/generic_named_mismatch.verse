# expect: 3:40: expected string, found int (in a call of Pick)
Pick(A:t, ?Other:t = A where t:type):t = Other
Main():void = Print(Pick("x", ?Other := 3))
