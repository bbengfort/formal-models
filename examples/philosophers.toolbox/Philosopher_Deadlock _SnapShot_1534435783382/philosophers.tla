---------------------------- MODULE philosophers ----------------------------

(*
  Dining philosophers problem: philsophers are sitting around a table with one 
  chopstick between each of them. Each philospher can pick up one stick at a  
  time, and if they have two sticks they can eat. A philosopher will only put
  their sticks down when they have eaten. 
  
  1. Show this deadlocks
  2. Assume they can put down a fork without eating, show livelock (no one eats)
*)

EXTENDS TLC, Integers, Sequences, FiniteSets  

\* Define constants and their assumptions for the model 
CONSTANT NPhilosophers
ASSUME NPhilosophers \in Nat  
 
\* Sequence friendly modulo 
a %% b == IF a % b = 0 THEN b ELSE a % b

\* PlusCal is used to implement the philosophers algorithm 
(*--algorithm dining 
variables
  sticks = [x \in 1..NPhilosophers |-> FALSE]; \* one stick per philosopher, each starting unused (down)   

fair process philosopher \in 1..NPhilosophers 
variables 
  left = IF self > 1 THEN self-1 ELSE Len(sticks);
  right = self;   

begin   
  PickUpLeft:   
    await ~sticks[left];
    sticks[left] := TRUE; 
  CheckRight:
    if ~sticks[right] then 
      sticks[right] := TRUE; 
    else  
      sticks[left] := FALSE; 
      goto PickUpLeft; 
    end if;   
  Eat:
    skip; 
  Finish:
    sticks[left] := FALSE || sticks[right] := FALSE;
end process;  

end algorithm; *) 


\* BEGIN TRANSLATION
VARIABLES sticks, pc, left, right

vars == << sticks, pc, left, right >>

ProcSet == (1..NPhilosophers)

Init == (* Global variables *)
        /\ sticks = [x \in 1..NPhilosophers |-> FALSE]
        (* Process philosopher *)
        /\ left = [self \in 1..NPhilosophers |-> IF self > 1 THEN self-1 ELSE Len(sticks)]
        /\ right = [self \in 1..NPhilosophers |-> self]
        /\ pc = [self \in ProcSet |-> "PickUpLeft"]

PickUpLeft(self) == /\ pc[self] = "PickUpLeft"
                    /\ ~sticks[left[self]]
                    /\ sticks' = [sticks EXCEPT ![left[self]] = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "CheckRight"]
                    /\ UNCHANGED << left, right >>

CheckRight(self) == /\ pc[self] = "CheckRight"
                    /\ IF ~sticks[right[self]]
                          THEN /\ sticks' = [sticks EXCEPT ![right[self]] = TRUE]
                               /\ pc' = [pc EXCEPT ![self] = "Eat"]
                          ELSE /\ sticks' = [sticks EXCEPT ![left[self]] = FALSE]
                               /\ pc' = [pc EXCEPT ![self] = "PickUpLeft"]
                    /\ UNCHANGED << left, right >>

Eat(self) == /\ pc[self] = "Eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Finish"]
             /\ UNCHANGED << sticks, left, right >>

Finish(self) == /\ pc[self] = "Finish"
                /\ sticks' = [sticks EXCEPT ![left[self]] = FALSE,
                                            ![right[self]] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << left, right >>

philosopher(self) == PickUpLeft(self) \/ CheckRight(self) \/ Eat(self)
                        \/ Finish(self)

Next == (\E self \in 1..NPhilosophers: philosopher(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NPhilosophers : WF_vars(philosopher(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* LIVENESS PROPERTIES 
\* Must be defined after the translation

\* Liveness here means that all of the philosophers end up eating at least once. 
Liveness == 
  \A p \in ProcSet:
    <>(pc[p] = "Eat") 


=============================================================================
\* Modification History
\* Last modified Thu Aug 16 12:09:34 EDT 2018 by benjamin
\* Created Thu Aug 16 11:22:55 EDT 2018 by benjamin
