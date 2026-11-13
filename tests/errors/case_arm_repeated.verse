# expect: this case arm is never reached: an earlier arm has the same pattern
Name(N:int):string =
    case (N):
        1 => "one"
        2 => "two"
        1 => "uno"
        _ => "many"
Main():void = Print(Name(1))
