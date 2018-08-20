-------------------------------- MODULE wire --------------------------------

EXTENDS Integers \* Add subtract
CONSTANTS People, MoneyRange 

(*--algorithm wire_alg 

\* global variables 
variables 
  account \in [People -> MoneyRange]; 
\*  total = alice + bob; 
  
\* add raw TLA+
define 
  NoOverdrafts == 
    \A p \in People: account[p] >= 0     
    
\*  BanksWork ==
\*  \* ascii for diamond box (diamond is eventually true, box means always true) 
\*  \* 
\*   <>[](total = alice + bob)   
end define; 

process wire \in {"t1", "t2"}  
\* local variables to wire process  
variables
  sender \in People; 
  recipient \in People \ {sender}; 
  transfer \in {1, 2, 3};
begin
  CheckAndWithdraw:
    if account[sender] >= transfer then
        account[sender] := account[sender] - transfer;
      Deposit:
        account[recipient] := account[recipient] + transfer;
  end if;   
end process  
  
end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES account, pc

(* define statement *)
NoOverdrafts ==
  \A p \in People: account[p] >= 0

VARIABLES sender, recipient, transfer

vars == << account, pc, sender, recipient, transfer >>

ProcSet == ({"t1", "t2"})

Init == (* Global variables *)
        /\ account \in [People -> MoneyRange]
        (* Process wire *)
        /\ sender \in [{"t1", "t2"} -> People]
        /\ recipient \in [{"t1", "t2"} -> People \ {sender[CHOOSE self \in  {"t1", "t2"} : TRUE]}]
        /\ transfer \in [{"t1", "t2"} -> {1, 2, 3}]
        /\ pc = [self \in ProcSet |-> "CheckAndWithdraw"]

CheckAndWithdraw(self) == /\ pc[self] = "CheckAndWithdraw"
                          /\ IF account[sender[self]] >= transfer[self]
                                THEN /\ account' = [account EXCEPT ![sender[self]] = account[sender[self]] - transfer[self]]
                                     /\ pc' = [pc EXCEPT ![self] = "Deposit"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ UNCHANGED account
                          /\ UNCHANGED << sender, recipient, transfer >>

Deposit(self) == /\ pc[self] = "Deposit"
                 /\ account' = [account EXCEPT ![recipient[self]] = account[recipient[self]] + transfer[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << sender, recipient, transfer >>

wire(self) == CheckAndWithdraw(self) \/ Deposit(self)

Next == (\E self \in {"t1", "t2"}: wire(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 18:08:31 EDT 2018 by benjamin
\* Created Tue Aug 14 10:52:24 EDT 2018 by benjamin
