-------------------------------- MODULE wire --------------------------------

EXTENDS Integers \* Add subtract

(*--algorithm wire_alg 

\* global variables 
variables 
  alice = 2; \* dollars  
  bob = 2; 
  
\* add raw TLA+
define 
  NoOverdrafts == 
    /\ alice >= 0 
    /\ bob >= 0 
end define; 

process wire \in {"t1", "t2"}  
\* local variables to wire process  
variables
  transfer \in {1, 2, 3};
begin
  CheckAndWithdraw:
    if alice >= transfer then
        alice := alice - transfer;
      Depoist:
        bob := bob + transfer;
  end if;   
end process  
  
end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES alice, bob, pc

(* define statement *)
NoOverdrafts ==
  /\ alice >= 0
  /\ bob >= 0

VARIABLE transfer

vars == << alice, bob, pc, transfer >>

ProcSet == ({"t1", "t2"})

Init == (* Global variables *)
        /\ alice = 2
        /\ bob = 2
        (* Process wire *)
        /\ transfer \in [{"t1", "t2"} -> {1, 2, 3}]
        /\ pc = [self \in ProcSet |-> "CheckAndWithdraw"]

CheckAndWithdraw(self) == /\ pc[self] = "CheckAndWithdraw"
                          /\ IF alice >= transfer[self]
                                THEN /\ alice' = alice - transfer[self]
                                     /\ pc' = [pc EXCEPT ![self] = "Depoist"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ alice' = alice
                          /\ UNCHANGED << bob, transfer >>

Depoist(self) == /\ pc[self] = "Depoist"
                 /\ bob' = bob + transfer[self]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << alice, transfer >>

wire(self) == CheckAndWithdraw(self) \/ Depoist(self)

Next == (\E self \in {"t1", "t2"}: wire(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 11:31:54 EDT 2018 by benjamin
\* Created Tue Aug 14 10:52:24 EDT 2018 by benjamin
