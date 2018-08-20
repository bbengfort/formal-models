----------------------------- MODULE semaphore -----------------------------

EXTENDS Integers, TLC, Sequences
CONSTANT Threads  

(*--algorithm semaphore 
variables 
  counter = 1; \* counter starts unlocked  
  
define 
  TypeInvariant == 
    counter \in 0..1
end define;

(*
SEMAPHORE SEMANTICS:
  1. IF COUNTER IS ZERO, THEN BLOCK 
  2. IF NONZERO, DECREMENT COUNTER, GO INTO CRITICAL SECTION 
  3. INCREMENT COUNTER
*)
process thread \in Threads begin
Start:
  await counter > 0;
  counter := counter - 1;  
CS:
  skip; 
Finish:
  counter := counter + 1; 
  goto Start;  
end process; 

end algorithm; *) 

\* BEGIN TRANSLATION
VARIABLES counter, pc

vars == << counter, pc >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 1
        /\ pc = [self \in ProcSet |-> "Start"]

Start(self) == /\ pc[self] = "Start"
               /\ counter > 0
               /\ counter' = counter - 1
               /\ pc' = [pc EXCEPT ![self] = "CS"]

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Finish"]
            /\ UNCHANGED counter

Finish(self) == /\ pc[self] = "Finish"
                /\ counter' = counter + 1
                /\ pc' = [pc EXCEPT ![self] = "Start"]

thread(self) == Start(self) \/ CS(self) \/ Finish(self)

Next == (\E self \in Threads: thread(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


\* Invariants must go after translation 
\* For all pairs of threads, if they aren't the same, they both can't be in the critical section.  
AtMostOneCriticalSection == 
  \A t1, t2 \in Threads: 
    t1 # t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS") 

=============================================================================
\* Modification History
\* Last modified Wed Aug 15 18:05:42 EDT 2018 by benjamin
\* Created Wed Aug 15 17:56:34 EDT 2018 by benjamin
