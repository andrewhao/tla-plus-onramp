----------------------------- MODULE HelloWorld -----------------------------
EXTENDS TLC

(* --algorithm HelloWorld
begin 
  A:
    print {"Hello", "World"}
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8e0661a9" /\ chksum(tla) = "11327d74")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "A"

A == /\ pc = "A"
     /\ PrintT({"Hello", "World"})
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Aug 06 21:20:05 PDT 2021 by andrewhao
\* Created Fri Aug 06 21:15:54 PDT 2021 by andrewhao
