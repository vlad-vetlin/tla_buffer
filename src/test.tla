---- MODULE test ----
EXTENDS Integers, TLC, Sequences, FiniteSets
CONSTANTS BuffLen, Threads
ASSUME BuffLen \in Nat
ASSUME Cardinality(Threads) >= 2

(* --algorithm test
variables
    Getters \in (SUBSET(Threads)) \ {{}, Threads};
    Putters = Threads \ Getters;
    buffer = <<>>;
    put_at = 1;
    get_at = 1;
    awake = [t \in Threads |-> TRUE];
    occupied = 0;
    define
        IsFull == occupied = BuffLen
        IsEmpty == occupied = 0
        SleepingPutterThreads == {t \in Putters: ~awake[t]}
        SleepingGetterThreads == {t \in Getters: ~awake[t]}
    end define;

    macro notifyPutter() begin
        if SleepingPutterThreads /= {} then
            with t \in SleepingPutterThreads do
                awake[t] := TRUE;
            end with;
        end if;
    end macro;

    macro notifyGetter() begin
        if SleepingGetterThreads /= {} then
            with t \in SleepingGetterThreads do
                awake[t] := TRUE;
            end with;
        end if;
    end macro;

    process get \in Getters
    begin Get:
        await awake[self];
        if IsEmpty then
            awake[self] := FALSE;
        else
            notifyPutter();
            occupied := occupied - 1;
        end if;
        goto Get;
    end process;

    process put \in Putters
    begin Put:
        await awake[self];
        if IsFull then
            awake[self] := FALSE;
        else
           notifyGetter();
           occupied := occupied + 1;
        end if;
        goto Put;
    end process;
end algorithm
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e297353b" /\ chksum(tla) = "fb500591")
VARIABLES Getters, Putters, kek, buffer, put_at, get_at, awake, occupied, pc

(* define statement *)
IsFull == occupied = BuffLen
IsEmpty == occupied = 0
SleepingPutterThreads == {t \in Putters: ~awake[t]}
SleepingGetterThreads == {t \in Getters: ~awake[t]}


vars == << Getters, Putters, kek, buffer, put_at, get_at, awake, occupied, pc
        >>

ProcSet == (Getters) \cup (Putters)

Init == (* Global variables *)
        /\ Getters \in (SUBSET(Threads)) \ {{}, Threads}
        /\ Putters = Threads \ Getters
        /\ kek = ""
        /\ buffer = <<>>
        /\ put_at = 1
        /\ get_at = 1
        /\ awake = [t \in Threads |-> TRUE]
        /\ occupied = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Getters -> "Get"
                                        [] self \in Putters -> "Put"]

Get(self) == /\ pc[self] = "Get"
             /\ awake[self]
             /\ IF IsEmpty
                   THEN /\ awake' = [awake EXCEPT ![self] = FALSE]
                        /\ kek' = "GET_SLEEP"
                        /\ UNCHANGED occupied
                   ELSE /\ IF SleepingPutterThreads /= {}
                              THEN /\ \E t \in SleepingPutterThreads:
                                        awake' = [awake EXCEPT ![t] = TRUE]
                              ELSE /\ TRUE
                                   /\ awake' = awake
                        /\ occupied' = occupied - 1
                        /\ kek' = "GET_NOTIFY"
             /\ pc' = [pc EXCEPT ![self] = "Get"]
             /\ UNCHANGED << Getters, Putters, buffer, put_at, get_at >>

get(self) == Get(self)

Put(self) == /\ pc[self] = "Put"
             /\ awake[self]
             /\ IF IsFull
                   THEN /\ awake' = [awake EXCEPT ![self] = FALSE]
                        /\ kek' = "PUT_SLEEP"
                        /\ UNCHANGED occupied
                   ELSE /\ IF SleepingGetterThreads /= {}
                              THEN /\ \E t \in SleepingGetterThreads:
                                        awake' = [awake EXCEPT ![t] = TRUE]
                              ELSE /\ TRUE
                                   /\ awake' = awake
                        /\ occupied' = occupied + 1
                        /\ kek' = "PUT_NOTIFY"
             /\ pc' = [pc EXCEPT ![self] = "Put"]
             /\ UNCHANGED << Getters, Putters, buffer, put_at, get_at >>

put(self) == Put(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Getters: get(self))
           \/ (\E self \in Putters: put(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
