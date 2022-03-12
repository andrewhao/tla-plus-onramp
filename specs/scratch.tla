------------------------------- MODULE Wires -------------------------------
EXTENDS Integers
(*--algorithm wire
variables
    banks = {"us", "them"},
    acc = [b \in banks |-> 5];
define
    NoOverdrafts == \A b \in banks: acc[p] >= 0
end define;
begin
    TransferMoney:
        if amount < acc[sender] then
                acc[sender] := acc[sender] - amount;
            Deposit:
                acc[receiver] := acc[receiver] + amount;
        end if;
\*CheckFunds:
\*    if amount <= acc[sender] then
\*        Withdraw:
\*            acc[sender] := acc[sender] - amount;
\*        Deposit:
\*            acc[receiver] := acc[receiver] + amount;
\*    end if;

end process;
end algorithm;*)