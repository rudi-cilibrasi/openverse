# Module-scoped var (Book of Verse ch. 3, "Module-Scoped weak_map Variables";
# ch. 16, ch. 17, ch. 18; docs/research/weak-map.md): a weak_map keyed by a
# class with <module_scoped_var_weak_map_key>, read and written one entry at
# a time, its writes undone by a failure context. With a <persistent> key its
# values persist (here a <persistable> struct and an array of ints). The
# example is the Book's ch. 17 "Example" and ch. 3 block 75, with the key
# class of the tests in place of the engine's persistent_key.

key := class<unique><persistent><module_scoped_var_weak_map_key>:
    Id:int

player_stats := struct<persistable>:
    Level:int = 1
    Experience:int = 0

progress_tracker := module:
    var Stats<public>:weak_map(key, player_stats) = map{}

    # a key with nothing saved yet gets the struct's defaults
    GetStats<public>(Key:key)<transacts>:player_stats =
        if (Existing := Stats[Key]) then Existing else player_stats{}

    AddExperience<public>(Key:key, Points:int)<transacts><decides>:void =
        Current := GetStats(Key)
        set Stats[Key] = player_stats:
            Level := Current.Level
            Experience := Current.Experience + Points

inventory := module:
    var Items<public>:weak_map(key, []int) = map{}

    Restock<public>(Key:key)<transacts><decides>:void =
        set Items[Key] = array{1, 2, 3}    # replace the whole value
        set Items[Key][0] = 99             # update one element inside it

Show(K:key)<transacts>:void =
    S := progress_tracker.GetStats(K)
    Print("key {K.Id}: level {S.Level}, experience {S.Experience}")

ShowItems(K:key)<transacts>:void =
    if (I := inventory.Items[K], X := I[0], Y := I[1], Z := I[2]) then Print("items of {K.Id}: {X} {Y} {Z}")
    else Print("no items for {K.Id}")

Main():void =
    A := key{Id := 1}
    B := key{Id := 2}
    Show(A)
    if (progress_tracker.AddExperience[A, 10]) {}
    if (progress_tracker.AddExperience[A, 5]) {}
    Show(A)
    Show(B)
    # a failure undoes the entries written, of both keys
    if:
        progress_tracker.AddExperience[B, 7]
        set progress_tracker.Stats[A] = player_stats{Level := 9, Experience := 9}
        false?
    Show(A)
    Show(B)
    if (inventory.Restock[B]) {}
    ShowItems(B)
    ShowItems(A)
    if (set inventory.Items[B][1] += 40) {}
    ShowItems(B)
