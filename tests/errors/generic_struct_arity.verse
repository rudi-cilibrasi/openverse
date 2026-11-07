# expect: pair takes 2 type argument(s), found 1
pair(t:type, u:type) := struct:
    First:t
    Second:u

Main():void =
    P:pair(int) = pair(int){First := 1}
