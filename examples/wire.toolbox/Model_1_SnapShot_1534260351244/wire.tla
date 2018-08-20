-------------------------------- MODULE wire --------------------------------

EXTENDS Integers \* Add subtract

(*--algorithm wire_alg 

variables 
  alice = 2; \* dollars  
  bob = 2; 
  transfer \in {1, 2, 3};
  
\* add raw TLA+
define 
  NoOverdrafts == 
    /\ alice >= 0 
    /\ bob >= 0 
end define; 

process transfer = "xfer"  
begin
  Check:
    if alice >= transfer then
      Withdraw:
        alice := alice - transfer;
      Depoist:
        bob := bob + transfer;
  end if;   
end process  
  
end algorithm; *)


\* BEGIN TRANSLATION
\* Process transfer at line 19 col 1 changed to transfer_
VARIABLES alice, bob, transfer, pc

(* define statement *)
NoOverdrafts ==
  /\ alice >= 0
  /\ bob >= 0


vars == << alice, bob, transfer, pc >>

ProcSet == {"xfer"}

Init == (* Global variables *)
        /\ alice = 2
        /\ bob = 2
        /\ transfer \in {1, 2, 3}
        /\ pc = [self \in ProcSet |-> "Check"]

Check == /\ pc["xfer"] = "Check"
         /\ IF alice >= transfer
               THEN /\ pc' = [pc EXCEPT !["xfer"] = "Withdraw"]
               ELSE /\ pc' = [pc EXCEPT !["xfer"] = "Done"]
         /\ UNCHANGED << alice, bob, transfer >>

Withdraw == /\ pc["xfer"] = "Withdraw"
            /\ alice' = alice - transfer
            /\ pc' = [pc EXCEPT !["xfer"] = "Depoist"]
            /\ UNCHANGED << bob, transfer >>

Depoist == /\ pc["xfer"] = "Depoist"
           /\ bob' = bob + transfer
           /\ pc' = [pc EXCEPT !["xfer"] = "Done"]
           /\ UNCHANGED << alice, transfer >>

transfer_ == Check \/ Withdraw \/ Depoist

Next == transfer_
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 11:25:29 EDT 2018 by benjamin
\* Created Tue Aug 14 10:52:24 EDT 2018 by benjamin
