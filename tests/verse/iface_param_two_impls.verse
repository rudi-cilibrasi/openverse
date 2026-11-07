# regression test from the #53 review (p35)
holder(t:type) := interface:
    Items:[]t = array{}
    Count():int = Items.Length
box(t:type) := class(holder(t)):
    Items<override>:[]t = array{}
intbox := class(holder(int)):
    Items<override>:[]int = array{1, 2, 3}
Main():void =
    A:holder(int) = intbox{}
    Print("{A.Count()}")
    B:holder(string) = box(string){Items := array{"a"}}
    Print("{B.Count()}")
    for (X : A.Items) { Print("{X}") }
