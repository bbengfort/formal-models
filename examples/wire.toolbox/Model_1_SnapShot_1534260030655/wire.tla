-------------------------------- MODULE wire --------------------------------

EXTENDS Integers \* Add subtract

(*--algorithm wire_alg 

variables 
  alice \in 0..5; \* dollars  
  bob \ in 0..5; 
  transfer \in 0..10;
  
\* add raw TLA+
define 
  NoOverdrafts == 
    /\ alice >= 0 
    /\ bob >= 0 
end define; 
  
begin
  if alice - transfer >= 0 then
    alice := alice - transfer;
    bob := bob + transfer;
  end if;   
end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES alice, bob, transfer, pc

(* define statement *)
NoOverdrafts ==
  /\ alice >= 0
  /\ bob >= 0


vars == << alice, bob, transfer, pc >>

Init == (* Global variables *)
        /\ alice = 2
        /\ bob = 2
        /\ transfer \in 1..3
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF alice - transfer >= 0
               THEN /\ alice' = alice - transfer
                    /\ bob' = bob + transfer
               ELSE /\ TRUE
                    /\ UNCHANGED << alice, bob >>
         /\ pc' = "Done"
         /\ UNCHANGED transfer

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 11:20:23 EDT 2018 by benjamin
\* Created Tue Aug 14 10:52:24 EDT 2018 by benjamin
