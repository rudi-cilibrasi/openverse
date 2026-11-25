# Err with a message stops the program with a runtime error (run alone,
# last: it ends the session).
# Tests LANGUAGE.md, Built-ins: "Err() and Err(Message) (stops the program;
# ch. 8: "a runtime error with an optional message" ...)"; Epic's digest:
# Err(Message:string)<computes>:false. The line after it is never printed.
# OpenVerse prints (Lean and C agree):
#   before err | then runtime-error (exit 2): error: user
Main()<suspends>:void =
    Print("OVPROBE before err")
    Sleep(0.0)
    X:int = Err("probe stop")
    Print("OVPROBE after err {X}")
