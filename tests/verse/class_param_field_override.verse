# regression test from the #39 review (p26_fieldover)
base(t:type) := class:
    var Items:[]t = array{}
sub(u:type) := class(base(u)):
    var Items<override>:[]u = array{}
Main():void =
    S := sub(int){}
    Print("{S.Items.Length}")
