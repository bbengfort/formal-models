-------------------------------- MODULE door --------------------------------

(*
  Abstract State Machine 
  ----------------------
  
  Abstract state machines are usually what we talk about in TLA+. We can specify 
  this using either to show all states and all state transitions, relying on the 
  await keyword to remove impossible transitions.  
*)

(*--algorithm door 
variables 
  open \in BOOLEAN;
  key \in BOOLEAN;  
  lock = FALSE; 

begin
  while TRUE do 
    either 
      \* Unlock 
      await lock;
      await (open \/ key);  
      lock := FALSE; 
    or 
      \* Lock 
      await ~lock; 
      await (open \/ key); 
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
  end while;  
end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES open, lock

vars == << open, lock >>

Init == (* Global variables *)
        /\ open \in BOOLEAN
        /\ lock \in BOOLEAN

Next == \/ /\ lock
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

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Aug 16 13:19:31 EDT 2018 by benjamin
\* Created Thu Aug 16 13:06:30 EDT 2018 by benjamin
