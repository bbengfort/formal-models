-------------------------------- MODULE door --------------------------------

(*
  Distributed State Machine 
  -------------------------
  
  Abstract state machines are usually what we talk about in TLA+. 
  
  
*)

(*--algorithm door 
variables 
  open \in BOOLEAN; 
  lock \in BOOLEAN; 

begin
  either 
    \* Unlock 
    await lock; 
    lock := FALSE; 
  or 
    \* Lock 
    await ~lock; 
    lock := TRUE 
  or 
    \* Open 
    await ~lock; 
    await ~open; 
    open := TRUE 
  or 
    \* Close 
    await open; 
    open := FALSE 
  end either; 
end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES open, lock, pc

vars == << open, lock, pc >>

Init == (* Global variables *)
        /\ open \in BOOLEAN
        /\ lock \in BOOLEAN
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \/ /\ lock
               /\ lock' = FALSE
               /\ open' = open
            \/ /\ ~lock
               /\ lock' = TRUE
               /\ open' = open
            \/ /\ ~lock
               /\ ~open
               /\ open' = TRUE
               /\ lock' = lock
            \/ /\ open
               /\ open' = FALSE
               /\ lock' = lock
         /\ pc' = "Done"

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Aug 16 13:11:13 EDT 2018 by benjamin
\* Created Thu Aug 16 13:06:30 EDT 2018 by benjamin
