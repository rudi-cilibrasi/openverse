# regression test from the #53 review (p37c)
holder(t:type) := interface:
    Item:t
intbox := class(holder(int)):
    Extra:int = 0
Use(H:holder(t) where t:type):t = H.Item
Main():void =
    Print("{Use(intbox{Item := 4}) + 2}")
