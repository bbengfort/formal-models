---------------------------- MODULE philosophers ----------------------------

(*
  Dining philosophers problem: philsophers are sitting around a table with one 
  chopstick between each of them. Each philospher can pick up one stick at a  
  time, and if they have two sticks they can eat. A philosopher will only put
  their sticks down when they have eaten. 
  
  1. Show this deadlocks
  2. Assume they can put down a fork without eating, show livelock (no one eats)
  3. All philosophers pick up left then right; but one picks up right then left 
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


define 
  StickAvailable(stick) == ~sticks[stick]
end define; 

macro pickup(stick) begin
  sticks[stick] := TRUE;
end macro; 

macro putdown(stick) begin
  sticks[stick] := FALSE
end macro; 

macro putdown_both() begin 
  sticks[left] := FALSE  || sticks[right] := FALSE; 
end macro; 

fair process philosopher \in 1..(NPhilosophers-1) 
variables 
  left = IF self > 1 THEN self-1 ELSE Len(sticks);
  right = self;   

begin   
  PickUpLeft:   
    await StickAvailable(left);
    pickup(left); 
  PickUpRight:
    if StickAvailable(right) then 
      pickup(right);
    else  
      putdown(left); 
      goto PickUpLeft; 
    end if;   
  Eat:
    skip; 
  Finish:
    putdown_both(); 
end process;  

fair process lh_philosopher \in {NPhilosophers} 
variables 
  left = IF self > 1 THEN self-1 ELSE Len(sticks);
  right = self;   

begin   
  LHPickUpRight:   
    await StickAvailable(right);
    pickup(right); 
  LHPickUpLeft:
    if StickAvailable(left) then 
      pickup(left);
    else  
      putdown(right); 
      goto PickUpRight; 
    end if;   
  LHEat:
    skip; 
  LHFinish:
    putdown_both(); 
end process; 


end algorithm; *) 


\* BEGIN TRANSLATION
\* Label PickUpLeft of process philosopher at line 52 col 5 changed to PickUpLeft_
\* Label PickUpRight of process philosopher at line 55 col 5 changed to PickUpRight_
\* Label Eat of process philosopher at line 62 col 5 changed to Eat_
\* Label Finish of process philosopher at line 42 col 3 changed to Finish_
\* Process variable left of process philosopher at line 47 col 3 changed to left_
\* Process variable right of process philosopher at line 48 col 3 changed to right_
VARIABLES sticks, pc

(* define statement *)
StickAvailable(stick) == ~sticks[stick]

VARIABLES left_, right_, left, right

vars == << sticks, pc, left_, right_, left, right >>

ProcSet == (1..(NPhilosophers-1)) \cup ({NPhilosophers})

Init == (* Global variables *)
        /\ sticks = [x \in 1..NPhilosophers |-> FALSE]
        (* Process philosopher *)
        /\ left_ = [self \in 1..(NPhilosophers-1) |-> IF self > 1 THEN self-1 ELSE Len(sticks)]
        /\ right_ = [self \in 1..(NPhilosophers-1) |-> self]
        (* Process lh_philosopher *)
        /\ left = [self \in {NPhilosophers} |-> IF self > 1 THEN self-1 ELSE Len(sticks)]
        /\ right = [self \in {NPhilosophers} |-> self]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..(NPhilosophers-1) -> "PickUpLeft_"
                                        [] self \in {NPhilosophers} -> "PickUpRight"]

PickUpLeft_(self) == /\ pc[self] = "PickUpLeft_"
                     /\ StickAvailable(left_[self])
                     /\ sticks' = [sticks EXCEPT ![left_[self]] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "PickUpRight_"]
                     /\ UNCHANGED << left_, right_, left, right >>

PickUpRight_(self) == /\ pc[self] = "PickUpRight_"
                      /\ IF StickAvailable(right_[self])
                            THEN /\ sticks' = [sticks EXCEPT ![right_[self]] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "Eat_"]
                            ELSE /\ sticks' = [sticks EXCEPT ![left_[self]] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "PickUpLeft_"]
                      /\ UNCHANGED << left_, right_, left, right >>

Eat_(self) == /\ pc[self] = "Eat_"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "Finish_"]
              /\ UNCHANGED << sticks, left_, right_, left, right >>

Finish_(self) == /\ pc[self] = "Finish_"
                 /\ sticks' = [sticks EXCEPT ![left_[self]] = FALSE,
                                             ![right_[self]] = FALSE]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << left_, right_, left, right >>

philosopher(self) == PickUpLeft_(self) \/ PickUpRight_(self) \/ Eat_(self)
                        \/ Finish_(self)

PickUpRight(self) == /\ pc[self] = "PickUpRight"
                     /\ StickAvailable(right[self])
                     /\ sticks' = [sticks EXCEPT ![right[self]] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "PickUpLeft"]
                     /\ UNCHANGED << left_, right_, left, right >>

PickUpLeft(self) == /\ pc[self] = "PickUpLeft"
                    /\ IF StickAvailable(left[self])
                          THEN /\ sticks' = [sticks EXCEPT ![left[self]] = TRUE]
                               /\ pc' = [pc EXCEPT ![self] = "Eat"]
                          ELSE /\ sticks' = [sticks EXCEPT ![right[self]] = FALSE]
                               /\ pc' = [pc EXCEPT ![self] = "PickUpRight"]
                    /\ UNCHANGED << left_, right_, left, right >>

Eat(self) == /\ pc[self] = "Eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Finish"]
             /\ UNCHANGED << sticks, left_, right_, left, right >>

Finish(self) == /\ pc[self] = "Finish"
                /\ sticks' = [sticks EXCEPT ![left[self]] = FALSE,
                                            ![right[self]] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << left_, right_, left, right >>

lh_philosopher(self) == PickUpRight(self) \/ PickUpLeft(self) \/ Eat(self)
                           \/ Finish(self)

Next == (\E self \in 1..(NPhilosophers-1): philosopher(self))
           \/ (\E self \in {NPhilosophers}: lh_philosopher(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..(NPhilosophers-1) : WF_vars(philosopher(self))
        /\ \A self \in {NPhilosophers} : WF_vars(lh_philosopher(self))

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
\* Last modified Thu Aug 16 12:25:06 EDT 2018 by benjamin
\* Created Thu Aug 16 11:22:55 EDT 2018 by benjamin
