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

process BankTransferAction \in {1, 2}
begin 
    ApproveTransfer:
        if external_balance >= 1 then
        \* Call the external service to debit
        either
          \* ...and it succeeds
          external_balance := external_balance - 1;

          \* Now turn to call the internal service
          either
            \* It succeeds
            internal_balance := internal_balance + 1;
          or
            \* It fails
            \* Now enqueue reversal
            skip
            
          end either;
        or
          \* The call to the external service fails
          \* TODO Do something
          external_balance := external_balance
        end either;     
        end if;
end process;

process ReversalWorker = 0
variable current_transaction;
begin DoReversal:
    while TRUE do
      await queue /= <<>>;
      current_transaction := Head(queue);
      queue := Tail(queue);
    end while;
end process;
 
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "ae76923d" /\ chksum(tla) = "9d1d5f0e")
CONSTANT defaultInitValue
VARIABLES queue, external_balance, internal_balance, pc

(* define statement *)
EventuallyConsistent == <>[](external_balance + internal_balance = 2)

VARIABLE current_transaction

vars == << queue, external_balance, internal_balance, pc, current_transaction
        >>

ProcSet == ({1, 2}) \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ external_balance = 2
        /\ internal_balance = 0
        (* Process ReversalWorker *)
        /\ current_transaction = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in {1, 2} -> "ApproveTransfer"
                                        [] self = 0 -> "DoReversal"]

ApproveTransfer(self) == /\ pc[self] = "ApproveTransfer"
                         /\ IF external_balance >= 1
                               THEN /\ \/ /\ external_balance' = external_balance - 1
                                          /\ \/ /\ internal_balance' = internal_balance + 1
                                             \/ /\ TRUE
                                                /\ UNCHANGED internal_balance
                                       \/ /\ external_balance' = external_balance
                                          /\ UNCHANGED internal_balance
                               ELSE /\ TRUE
                                    /\ UNCHANGED << external_balance, 
                                                    internal_balance >>
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << queue, current_transaction >>

BankTransferAction(self) == ApproveTransfer(self)

DoReversal == /\ pc[0] = "DoReversal"
              /\ queue /= <<>>
              /\ current_transaction' = Head(queue)
              /\ queue' = Tail(queue)
              /\ pc' = [pc EXCEPT ![0] = "DoReversal"]
              /\ UNCHANGED << external_balance, internal_balance >>

ReversalWorker == DoReversal

Next == ReversalWorker
           \/ (\E self \in {1, 2}: BankTransferAction(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Mar 08 21:15:09 PST 2022 by andrewhao
\* Created Wed Feb 23 22:30:47 PST 2022 by andrewhao
