# Book: Tests/Enum.versetest:171 (bp_vm_only): an enum of more than 256
# values (here 257, e000 to e100; the Book's has 768, two of them differing
# only in case, e1e1 and e1E1). The Book's Blueprint VM refuses it at link
# time, 3552, "a limitation of the BPVM implementation only"; the Verse VM
# twin (:233) is valid and agrees in OpenVerse, which prints
#   e100 compared
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: enum-wide-control (256 values).
wide := enum {
    e000,e001,e002,e003,e004,e005,e006,e007,e008,e009,e00A,e00B,e00C,e00D,e00E,e00F,
    e010,e011,e012,e013,e014,e015,e016,e017,e018,e019,e01A,e01B,e01C,e01D,e01E,e01F,
    e020,e021,e022,e023,e024,e025,e026,e027,e028,e029,e02A,e02B,e02C,e02D,e02E,e02F,
    e030,e031,e032,e033,e034,e035,e036,e037,e038,e039,e03A,e03B,e03C,e03D,e03E,e03F,
    e040,e041,e042,e043,e044,e045,e046,e047,e048,e049,e04A,e04B,e04C,e04D,e04E,e04F,
    e050,e051,e052,e053,e054,e055,e056,e057,e058,e059,e05A,e05B,e05C,e05D,e05E,e05F,
    e060,e061,e062,e063,e064,e065,e066,e067,e068,e069,e06A,e06B,e06C,e06D,e06E,e06F,
    e070,e071,e072,e073,e074,e075,e076,e077,e078,e079,e07A,e07B,e07C,e07D,e07E,e07F,
    e080,e081,e082,e083,e084,e085,e086,e087,e088,e089,e08A,e08B,e08C,e08D,e08E,e08F,
    e090,e091,e092,e093,e094,e095,e096,e097,e098,e099,e09A,e09B,e09C,e09D,e09E,e09F,
    e0A0,e0A1,e0A2,e0A3,e0A4,e0A5,e0A6,e0A7,e0A8,e0A9,e0AA,e0AB,e0AC,e0AD,e0AE,e0AF,
    e0B0,e0B1,e0B2,e0B3,e0B4,e0B5,e0B6,e0B7,e0B8,e0B9,e0BA,e0BB,e0BC,e0BD,e0BE,e0BF,
    e0C0,e0C1,e0C2,e0C3,e0C4,e0C5,e0C6,e0C7,e0C8,e0C9,e0CA,e0CB,e0CC,e0CD,e0CE,e0CF,
    e0D0,e0D1,e0D2,e0D3,e0D4,e0D5,e0D6,e0D7,e0D8,e0D9,e0DA,e0DB,e0DC,e0DD,e0DE,e0DF,
    e0E0,e0E1,e0E2,e0E3,e0E4,e0E5,e0E6,e0E7,e0E8,e0E9,e0EA,e0EB,e0EC,e0ED,e0EE,e0EF,
    e0F0,e0F1,e0F2,e0F3,e0F4,e0F5,e0F6,e0F7,e0F8,e0F9,e0FA,e0FB,e0FC,e0FD,e0FE,e0FF,
    e100
}

Main():void =
    V:wide = wide.e100
    if (V = wide.e100):
        Print("OVPROBE e100 compared")
