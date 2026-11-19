# Control of join-generic-effects-transacts: TransactsIdentity, generic, as
# a value of type{_(:int)<decides><transacts>:int}, no join. Book:
# Tests/Function.versetest:231 (valid on both VMs). OpenVerse prints
#   value 1
TransactsIdentity(X:t where t:type)<transacts>:t = X

Apply()<transacts><decides>:int =
    F:type{_(:int)<decides><transacts>:int} = TransactsIdentity
    F[1]

Main():void =
    if (V := Apply[]):
        Print("OVPROBE value {V}")
