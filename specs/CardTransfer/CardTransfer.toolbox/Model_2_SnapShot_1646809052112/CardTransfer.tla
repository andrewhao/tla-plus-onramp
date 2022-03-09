---------------------------- MODULE CardTransfer ----------------------------
EXTENDS TLC, Integers, Sequences
(*--algorithm transfer_bank_balance

variables
    queue = <<>>,
    external_balance = 10,
    internal_balance = 0;

define
    EventuallyConsistent == <>[](external_balance + internal_balance = 2)
    NeverOverdraft == external_balance >= 0
end define;

process BankTransferAction = 1
variables i = 0;
begin 
ApproveTransfer:
    while i < 100 do \* Sequential process of 5 "tries" from a single user
    ExternalTransfer:
        \* Call the external service to transfer. For simplicity's sake, we assume
        \* it always succeeds
        external_balance := external_balance - 1;
        \* Now turn to call the internal service
        either
        SuccessfulInternalTransfer:
            \* It succeeds
            internal_balance := internal_balance + 1;
        or
        FailedInternalTransfer:
        \* It fails
        \* Now enqueue reversal
          queue := Append(queue, 1);
        end either;

    IncrCounterTryAgain:
            i := i + 1;
    end while;


end process;

process ReversalWorker = 0
variable balance_to_restore;
begin
    DoReversal:
    while TRUE do
      if Len(queue) > 0 then
      balance_to_restore := Head(queue);
      queue := Tail(queue);
      external_balance := external_balance + balance_to_restore;
      end if;
    end while;
end process;
 
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "b112afef" /\ chksum(tla) = "2bcde370")
CONSTANT defaultInitValue
VARIABLES queue, external_balance, internal_balance, pc

(* define statement *)
EventuallyConsistent == <>[](external_balance + internal_balance = 2)
NeverOverdraft == external_balance >= 0

VARIABLES i, balance_to_restore

vars == << queue, external_balance, internal_balance, pc, i, 
           balance_to_restore >>

ProcSet == {1} \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ external_balance = 10
        /\ internal_balance = 0
        (* Process BankTransferAction *)
        /\ i = 0
        (* Process ReversalWorker *)
        /\ balance_to_restore = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "ApproveTransfer"
                                        [] self = 0 -> "DoReversal"]

ApproveTransfer == /\ pc[1] = "ApproveTransfer"
                   /\ IF i < 100
                         THEN /\ pc' = [pc EXCEPT ![1] = "ExternalTransfer"]
                         ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                   /\ UNCHANGED << queue, external_balance, internal_balance, 
                                   i, balance_to_restore >>

ExternalTransfer == /\ pc[1] = "ExternalTransfer"
                    /\ external_balance' = external_balance - 1
                    /\ \/ /\ pc' = [pc EXCEPT ![1] = "SuccessfulInternalTransfer"]
                       \/ /\ pc' = [pc EXCEPT ![1] = "FailedInternalTransfer"]
                    /\ UNCHANGED << queue, internal_balance, i, 
                                    balance_to_restore >>

SuccessfulInternalTransfer == /\ pc[1] = "SuccessfulInternalTransfer"
                              /\ internal_balance' = internal_balance + 1
                              /\ pc' = [pc EXCEPT ![1] = "IncrCounterTryAgain"]
                              /\ UNCHANGED << queue, external_balance, i, 
                                              balance_to_restore >>

FailedInternalTransfer == /\ pc[1] = "FailedInternalTransfer"
                          /\ queue' = Append(queue, 1)
                          /\ pc' = [pc EXCEPT ![1] = "IncrCounterTryAgain"]
                          /\ UNCHANGED << external_balance, internal_balance, 
                                          i, balance_to_restore >>

IncrCounterTryAgain == /\ pc[1] = "IncrCounterTryAgain"
                       /\ i' = i + 1
                       /\ pc' = [pc EXCEPT ![1] = "ApproveTransfer"]
                       /\ UNCHANGED << queue, external_balance, 
                                       internal_balance, balance_to_restore >>

BankTransferAction == ApproveTransfer \/ ExternalTransfer
                         \/ SuccessfulInternalTransfer
                         \/ FailedInternalTransfer \/ IncrCounterTryAgain

DoReversal == /\ pc[0] = "DoReversal"
              /\ IF Len(queue) > 0
                    THEN /\ balance_to_restore' = Head(queue)
                         /\ queue' = Tail(queue)
                         /\ external_balance' = external_balance + balance_to_restore'
                    ELSE /\ TRUE
                         /\ UNCHANGED << queue, external_balance, 
                                         balance_to_restore >>
              /\ pc' = [pc EXCEPT ![0] = "DoReversal"]
              /\ UNCHANGED << internal_balance, i >>

ReversalWorker == DoReversal

Next == BankTransferAction \/ ReversalWorker

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Mar 08 22:57:26 PST 2022 by andrewhao
\* Created Wed Feb 23 22:30:47 PST 2022 by andrewhao
