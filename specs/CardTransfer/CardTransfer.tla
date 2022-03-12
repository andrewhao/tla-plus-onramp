---------------------------- MODULE CardTransfer ----------------------------
EXTENDS TLC, Integers, Sequences
(*--algorithm transfer_bank_balance

variables
    queue = <<>>,
    reversal_in_progress = FALSE,
    transfer_amount = 5,
    button_mash_attempts = 0,
    external_balance = 10,
    internal_balance = 0;

define
    NeverOverdraft == external_balance >= 0
    EventuallyConsistentTransfer == <>[](external_balance + internal_balance = 10)
end define;


fair process BankTransferAction = "BankTransferAction"
begin
    ExternalTransfer:
        \* Call the external service to transfer. For simplicity's sake, we assume
        \* it always succeeds
        external_balance := external_balance - transfer_amount;
    InternalTransfer:
        \* Now turn to call the internal service
        either
          internal_balance := internal_balance + transfer_amount;
        or
          \* Internal system error!
          \* The system will enqueue the compensating reversal transaction.
          queue := Append(queue, transfer_amount);
          reversal_in_progress := TRUE;

          \* The user is impatient! Their transfer must go through.
          \* They button mash (up to 3 times)....
          UserButtonMash: 
\*            await reversal_in_progress = FALSE;         
            if (button_mash_attempts < 3) then
                \* But the UI blocks them from re-submitting until the transaction
                \* has finished being reversed/compensated.
                button_mash_attempts := button_mash_attempts + 1;
     
                goto ExternalTransfer;
            end if;
        end either;
end process;

\* This models an async task runner that will run a
\* a reversal compensating transaction.
fair process ReversalWorker = "ReversalWorker"
variable balance_to_restore = 0;
begin
    DoReversal:
      while TRUE do
         await queue /= <<>>;
         balance_to_restore := Head(queue);
         queue := Tail(queue);
         external_balance := external_balance + balance_to_restore;
         reversal_in_progress := FALSE;
      end while;


end process;
 
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cd861d71" /\ chksum(tla) = "27435b8f")
VARIABLES queue, reversal_in_progress, transfer_amount, button_mash_attempts, 
          external_balance, internal_balance, pc

(* define statement *)
NeverOverdraft == external_balance >= 0
EventuallyConsistentTransfer == <>[](external_balance + internal_balance = 10)

VARIABLE balance_to_restore

vars == << queue, reversal_in_progress, transfer_amount, button_mash_attempts, 
           external_balance, internal_balance, pc, balance_to_restore >>

ProcSet == {"BankTransferAction"} \cup {"ReversalWorker"}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ reversal_in_progress = FALSE
        /\ transfer_amount = 5
        /\ button_mash_attempts = 0
        /\ external_balance = 10
        /\ internal_balance = 0
        (* Process ReversalWorker *)
        /\ balance_to_restore = 0
        /\ pc = [self \in ProcSet |-> CASE self = "BankTransferAction" -> "ExternalTransfer"
                                        [] self = "ReversalWorker" -> "DoReversal"]

ExternalTransfer == /\ pc["BankTransferAction"] = "ExternalTransfer"
                    /\ external_balance' = external_balance - transfer_amount
                    /\ pc' = [pc EXCEPT !["BankTransferAction"] = "InternalTransfer"]
                    /\ UNCHANGED << queue, reversal_in_progress, 
                                    transfer_amount, button_mash_attempts, 
                                    internal_balance, balance_to_restore >>

InternalTransfer == /\ pc["BankTransferAction"] = "InternalTransfer"
                    /\ \/ /\ internal_balance' = internal_balance + transfer_amount
                          /\ pc' = [pc EXCEPT !["BankTransferAction"] = "Done"]
                          /\ UNCHANGED <<queue, reversal_in_progress>>
                       \/ /\ queue' = Append(queue, transfer_amount)
                          /\ reversal_in_progress' = TRUE
                          /\ pc' = [pc EXCEPT !["BankTransferAction"] = "UserButtonMash"]
                          /\ UNCHANGED internal_balance
                    /\ UNCHANGED << transfer_amount, button_mash_attempts, 
                                    external_balance, balance_to_restore >>

UserButtonMash == /\ pc["BankTransferAction"] = "UserButtonMash"
                  /\ IF (button_mash_attempts < 3)
                        THEN /\ button_mash_attempts' = button_mash_attempts + 1
                             /\ pc' = [pc EXCEPT !["BankTransferAction"] = "ExternalTransfer"]
                        ELSE /\ pc' = [pc EXCEPT !["BankTransferAction"] = "Done"]
                             /\ UNCHANGED button_mash_attempts
                  /\ UNCHANGED << queue, reversal_in_progress, transfer_amount, 
                                  external_balance, internal_balance, 
                                  balance_to_restore >>

BankTransferAction == ExternalTransfer \/ InternalTransfer
                         \/ UserButtonMash

DoReversal == /\ pc["ReversalWorker"] = "DoReversal"
              /\ queue /= <<>>
              /\ balance_to_restore' = Head(queue)
              /\ queue' = Tail(queue)
              /\ external_balance' = external_balance + balance_to_restore'
              /\ reversal_in_progress' = FALSE
              /\ pc' = [pc EXCEPT !["ReversalWorker"] = "DoReversal"]
              /\ UNCHANGED << transfer_amount, button_mash_attempts, 
                              internal_balance >>

ReversalWorker == DoReversal

Next == BankTransferAction \/ ReversalWorker

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(BankTransferAction)
        /\ WF_vars(ReversalWorker)

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Mar 11 22:19:43 PST 2022 by andrewhao
\* Created Wed Feb 23 22:30:47 PST 2022 by andrewhao
