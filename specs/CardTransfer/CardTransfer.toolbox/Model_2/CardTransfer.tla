---------------------------- MODULE CardTransfer ----------------------------
EXTENDS TLC, Integers, Sequences
(*--algorithm transfer_bank_balance

variables
    queue = <<>>,
    external_balance = 2,
    internal_balance = 0;

define
    EventuallyConsistent == <>[](external_balance + internal_balance = 2)
    NeverOverdraft == external_balance >= 0
end define;

process BankTransferAction \in 1..2
variables i = 0;
begin 
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
end process;

process ReversalWorker = 0
variable balance_to_restore;
begin
    PollReversal:
    while TRUE do
      await queue /= <<>>; \*if Len(queue) > 0 then
      DoReversal:
         balance_to_restore := Head(queue);
         queue := Tail(queue);
         external_balance := external_balance + balance_to_restore;
      \*end if;
    end while;
end process;
 
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "4c3d467" /\ chksum(tla) = "9d920bf7")
CONSTANT defaultInitValue
VARIABLES queue, external_balance, internal_balance, pc

(* define statement *)
EventuallyConsistent == <>[](external_balance + internal_balance = 2)
NeverOverdraft == external_balance >= 0

VARIABLES i, balance_to_restore

vars == << queue, external_balance, internal_balance, pc, i, 
           balance_to_restore >>

ProcSet == (1..2) \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ external_balance = 2
        /\ internal_balance = 0
        (* Process BankTransferAction *)
        /\ i = [self \in 1..2 |-> 0]
        (* Process ReversalWorker *)
        /\ balance_to_restore = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in 1..2 -> "ExternalTransfer"
                                        [] self = 0 -> "PollReversal"]

ExternalTransfer(self) == /\ pc[self] = "ExternalTransfer"
                          /\ external_balance' = external_balance - 1
                          /\ \/ /\ pc' = [pc EXCEPT ![self] = "SuccessfulInternalTransfer"]
                             \/ /\ pc' = [pc EXCEPT ![self] = "FailedInternalTransfer"]
                          /\ UNCHANGED << queue, internal_balance, i, 
                                          balance_to_restore >>

SuccessfulInternalTransfer(self) == /\ pc[self] = "SuccessfulInternalTransfer"
                                    /\ internal_balance' = internal_balance + 1
                                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << queue, external_balance, i, 
                                                    balance_to_restore >>

FailedInternalTransfer(self) == /\ pc[self] = "FailedInternalTransfer"
                                /\ queue' = Append(queue, 1)
                                /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << external_balance, 
                                                internal_balance, i, 
                                                balance_to_restore >>

BankTransferAction(self) == ExternalTransfer(self)
                               \/ SuccessfulInternalTransfer(self)
                               \/ FailedInternalTransfer(self)

PollReversal == /\ pc[0] = "PollReversal"
                /\ queue /= <<>>
                /\ pc' = [pc EXCEPT ![0] = "DoReversal"]
                /\ UNCHANGED << queue, external_balance, internal_balance, i, 
                                balance_to_restore >>

DoReversal == /\ pc[0] = "DoReversal"
              /\ balance_to_restore' = Head(queue)
              /\ queue' = Tail(queue)
              /\ external_balance' = external_balance + balance_to_restore'
              /\ pc' = [pc EXCEPT ![0] = "PollReversal"]
              /\ UNCHANGED << internal_balance, i >>

ReversalWorker == PollReversal \/ DoReversal

Next == ReversalWorker
           \/ (\E self \in 1..2: BankTransferAction(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Mar 08 23:20:18 PST 2022 by andrewhao
\* Created Wed Feb 23 22:30:47 PST 2022 by andrewhao
