# #704 follow-up: a module-scoped weak_map's entry, replaced by the right
# operand. For Epic only: OpenVerse has no session or GetSession and refuses
# this body; its own module-scoped entries (a <module_scoped_var_weak_map_key>
# class, tests/verse/set_op_place_object.verse) give "entry 8 9". Reading
# after the right operand: "entry 8 10".
var Entries:weak_map(session, []int) = map{}

Main()<transacts>:void =
    if (set Entries[GetSession()] = array{1, 2}):
        if (set Entries[GetSession()][1] += if (set Entries[GetSession()] = array{8, 9}; 0 = 0) then 1 else 1,
                E := Entries[GetSession()], A := E[0], B := E[1]):
            Print("OVPROBE entry {A} {B}")
        else:
            Print("OVPROBE update failed")
    else:
        Print("OVPROBE entry not set")
