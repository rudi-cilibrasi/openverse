# expect: starts a task with spawn{…}
# A field's default has no more effects than its class declares (Book of
# Verse ch. 13): a <computes> class's default cannot spawn
Child()<suspends><computes>:void=Sleep(0.01)
holder:=class<computes>:
    T:task(void)=spawn{Child()}
Main()<suspends>:void=
    H:=holder{}
    Sleep(0.1)
