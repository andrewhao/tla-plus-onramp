---------------------------- MODULE CardTransfer ----------------------------
EXTENDS TLC, Integers, Sequences
(*--algorithm transfer_bank_balance

variables
    queue = <<>>,
    external_balance = 2,
    internal_balance = 0;

define
    EventuallyConsistent == <>[](external_balance + internal_balance = 2)
end define;

process BankTransferAction \in 1..2
begin 
    ApproveTransfer:
        if external_balance > 1 then
          external_balance := external_balance - 1;
          internal_balance := internal_balance + 1;
        end if;
end process;

process reversal_worker = "reversal_worker"
variable current_transaction = <<>>;
begin DoReversal:
    while TRUE do
      await queue /= <<>>;
      current_transaction := Head(queue);
      queue := Tail(queue);
    end while;
end process;
 
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "507fd439" /\ chksum(tla) = "c06ee669")
VARIABLES queue, external_balance, internal_balance, pc

(* define statement *)
EventuallyConsistent == <>[](external_balance + internal_balance = 2)

VARIABLE current_transaction

vars == << queue, external_balance, internal_balance, pc, current_transaction
        >>

ProcSet == (1..2) \cup {"reversal_worker"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ external_balance = 2
        /\ internal_balance = 0
        (* Process reversal_worker *)
        /\ current_transaction = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> "ApproveTransfer"
                                        [] self = "reversal_worker" -> "DoReversal"]

ApproveTransfer(self) == /\ pc[self] = "ApproveTransfer"
                         /\ IF external_balance > 1
                               THEN /\ external_balance' = external_balance - 1
                                    /\ internal_balance' = internal_balance + 1
                               ELSE /\ TRUE
                                    /\ UNCHANGED << external_balance, 
                                                    internal_balance >>
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << queue, current_transaction >>

BankTransferAction(self) == ApproveTransfer(self)

DoReversal == /\ pc["reversal_worker"] = "DoReversal"
              /\ queue /= <<>>
              /\ current_transaction' = Head(queue)
              /\ queue' = Tail(queue)
              /\ pc' = [pc EXCEPT !["reversal_worker"] = "DoReversal"]
              /\ UNCHANGED << external_balance, internal_balance >>

reversal_worker == DoReversal

Next == reversal_worker
           \/ (\E self \in 1..2: BankTransferAction(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Mar 08 16:21:59 PST 2022 by andrewhao
\* Created Wed Feb 23 22:30:47 PST 2022 by andrewhao
