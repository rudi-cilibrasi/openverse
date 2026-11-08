# a generic function with roots used at large closed types: a struct of many fields, a tuple of nested structs (#174)
vec3 := struct:
    X:float = 0.0
    Y:float = 0.0
    Z:float = 0.0
transform := struct:
    Pos:vec3 = vec3{}
    Rot:vec3 = vec3{}
    Scale:vec3 = vec3{}
entity := struct:
    Name:string = "e"
    T:transform = transform{}
    Vel:vec3 = vec3{}
    Tags:[]string = array{}
    Health:int = 100
Later(X:t where t:type):task(t) = spawn{Echo(X)}
Echo(X:t where t:type)<suspends>:t =
    Sleep(0.1)
    X
Main()<suspends>:void =
    A := Later(entity{})
    Print("{A.Await().Health}")
