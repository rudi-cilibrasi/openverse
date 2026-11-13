# A float literal may end in the width suffix f64 (Book of Verse ch. 1, "Float
# Literals": `Explicit := 12.34f64`; its tests: `1234f64`, `1e5f64`).
Main():void =
    if (12.34f64 = 12.34, 1234f64 = 1234.0, 1.0e-10f64 = 1.0e-10, 1e5f64 = 1e5, -1.23f64 = -1.23):
        Print("{12.34f64} {1234f64}")
