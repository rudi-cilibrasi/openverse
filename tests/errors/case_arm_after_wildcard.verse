# expect: this case arm is never reached: it comes after _, which matches everything
color := enum{Red, Green, Blue}
Name(C:color):string =
    case (C):
        color.Red => "red"
        _ => "other"
        color.Blue => "blue"
Main():void = Print(Name(color.Blue))
