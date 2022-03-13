------------------------ MODULE TransactionIsolation ------------------------
EXTENDS TLC, Integers, Sequences
(*--algorithm xation_isolation

variables 
  transfer_amount = 500,
  account1 = 1000,
  account2 = 1000;

process User = "user"
begin
  StartUserTransfer:
    account1 := account1 + transfer_amount;
  FinalizeUserTransfer:
    account2 := account2 - transfer_amount;
end process;

process Auditor = "auditor"
begin
  DoAudit:
    assert account1 + account2 = 2000
end process;
    
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "fea4e677" /\ chksum(tla) = "6a7ea686")
VARIABLES transfer_amount, account1, account2, pc

vars == << transfer_amount, account1, account2, pc >>

ProcSet == {"user"} \cup {"auditor"}

Init == (* Global variables *)
        /\ transfer_amount = 500
        /\ account1 = 1000
        /\ account2 = 1000
        /\ pc = [self \in ProcSet |-> CASE self = "user" -> "StartUserTransfer"
                                        [] self = "auditor" -> "DoAudit"]

StartUserTransfer == /\ pc["user"] = "StartUserTransfer"
                     /\ account1' = account1 + transfer_amount
                     /\ pc' = [pc EXCEPT !["user"] = "FinalizeUserTransfer"]
                     /\ UNCHANGED << transfer_amount, account2 >>

FinalizeUserTransfer == /\ pc["user"] = "FinalizeUserTransfer"
                        /\ account2' = account2 - transfer_amount
                        /\ pc' = [pc EXCEPT !["user"] = "Done"]
                        /\ UNCHANGED << transfer_amount, account1 >>

User == StartUserTransfer \/ FinalizeUserTransfer

DoAudit == /\ pc["auditor"] = "DoAudit"
           /\ Assert(account1 + account2 = 2000, 
                     "Failure of assertion at line 21, column 5.")
           /\ pc' = [pc EXCEPT !["auditor"] = "Done"]
           /\ UNCHANGED << transfer_amount, account1, account2 >>

Auditor == DoAudit

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == User \/ Auditor
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Mar 12 16:27:45 PST 2022 by andrewhao
\* Created Sat Mar 12 16:21:58 PST 2022 by andrewhao
