------------------------------- MODULE dekker -------------------------------

(*
  We want to run two threads that have critical (C) and non critical (P) sections. 
  We want to prove that only one thread is in the critical section at a time, and 
  that at least one thread hits the critical section.  
*)

EXTENDS TLC, Integers 

(*--algorithm dekker 

variables 
  flags = <<FALSE, FALSE, FALSE>>;
  next = 1;
 
define 
  
end define;  

\* Very fine grained atomicity because each step is a hardware execution 
fair process thread \in {1,2,3} begin 
\* Request the lock to do the critical section 
P1: flags[self] := TRUE; 
P2: 
  \* Spin Lock (e.g. double checked locking) 
  while ~(\A f \in 1..3: ~flags[f] \/ (f = self)) do 
    P2_1: 
      if next # self then 
        P2_1_1: flags[self] := FALSE;
        P2_1_2: await next = self; \* tiebreak 
        P2_1_3: flags[self] := TRUE; 
      end if;  
  end while; 
\* Perform critical section 
CS: skip; 
\* Signal that we're done with the critical section
P3: 
  with n \in 1..3 do 
    next := n; 
  end with;
P4: flags[self] := FALSE;
P5: goto P1; 
end process; 

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES flags, next, pc

vars == << flags, next, pc >>

ProcSet == ({1,2,3})

Init == (* Global variables *)
        /\ flags = <<FALSE, FALSE, FALSE>>
        /\ next = 1
        /\ pc = [self \in ProcSet |-> "P1"]

P1(self) == /\ pc[self] = "P1"
            /\ flags' = [flags EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ next' = next

P2(self) == /\ pc[self] = "P2"
            /\ IF \A f \in 1..3: flags[f] = (f = self)
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flags, next >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ IF next # self
                    THEN /\ pc' = [pc EXCEPT ![self] = "P2_1_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << flags, next >>

P2_1_1(self) == /\ pc[self] = "P2_1_1"
                /\ flags' = [flags EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "P2_1_2"]
                /\ next' = next

P2_1_2(self) == /\ pc[self] = "P2_1_2"
                /\ next = self
                /\ pc' = [pc EXCEPT ![self] = "P2_1_3"]
                /\ UNCHANGED << flags, next >>

P2_1_3(self) == /\ pc[self] = "P2_1_3"
                /\ flags' = [flags EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "P2"]
                /\ next' = next

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flags, next >>

P3(self) == /\ pc[self] = "P3"
            /\ \E n \in 1..3:
                 next' = n
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ flags' = flags

P4(self) == /\ pc[self] = "P4"
            /\ flags' = [flags EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ next' = next

P5(self) == /\ pc[self] = "P5"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flags, next >>

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_1_1(self)
                   \/ P2_1_2(self) \/ P2_1_3(self) \/ CS(self) \/ P3(self)
                   \/ P4(self) \/ P5(self)

Next == (\E self \in {1,2,3}: thread(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1,2,3} : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


\* THIS MUST BE UNDER THE TRANSLATION SINCE WE'RE LOOKING AT THE PROGRAM COUNTER (pc) 
\*AtMostOneCritical == ~(pc[1] = "CS" /\ pc[2] = "CS")
AtMostOneCritical == ~(\A p \in ProcSet: pc[p] = "CS") 

(* above is equivalent to:  
AtMostOneCritical == 
  \/ pc[1] # "CS"
  \/ pc[2] # "CS"
*)

\* Create a temporal operator to ensure that all threads eventually get to critical section 
\*Liveness == 
\*  /\ <>(pc[1] = "CS") 
\*  /\ <>(pc[2] = "CS") 
  
Liveness == \A p \in ProcSet: <>(pc[p] = "CS")

=============================================================================
\* Modification History
\* Last modified Wed Aug 15 17:03:51 EDT 2018 by benjamin
\* Created Wed Aug 15 15:49:39 EDT 2018 by benjamin
