# expect: using a value of type type{_(:int)<computes>:int} as a value of type type{_(:int)<decides><computes>:int} is not yet implemented
# the branches of an if are the generic Identity <computes> and
# DecidesIdentity <computes><decides> at type{_(:int)<computes><decides>:int}:
# Identity's instance needs a wrapper that adds <decides> (UEFN 43.12, error
# 3502 at that branch: followup-book2/join-generic-effects-decides;
# Function.versetest:238, bp_vm_only). Named alone at the type, Identity is
# admitted (fn_coerce_generic_decides_control).
Identity(X:t where t:type)<computes>:t = X
DecidesIdentity(X:t where t:type)<computes><decides>:t = X
Pick(Flag:logic)<computes><decides>:int =
    F:type{_(:int)<computes><decides>:int} = if (Flag?) { Identity } else { DecidesIdentity }
    F[1]
Main():void =
    if (V := Pick[true]):
        Print("{V}")
