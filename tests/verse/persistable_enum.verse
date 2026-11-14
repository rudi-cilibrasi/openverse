# An enum marked <persistable> may be a field of a <persistable> struct
# (Book of Verse ch. 17, "Custom Persistable Types"); its <open> or <closed>
# beside it as before.
mode := enum<closed><persistable>:
    On
    Off
save := struct<persistable>:
    Score:int = 0
    Mode:mode = mode.Off
Show(M:mode):string = if (M = mode.On) then "on" else "off"
Main():void =
    S := save{Score := 3, Mode := mode.On}
    Print("{S.Score} {Show(S.Mode)} {Show(save{}.Mode)}")
