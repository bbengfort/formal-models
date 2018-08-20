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
  \* A stick is available if it's unused (FALSE)
  StickAvailable(stick) == ~sticks[stick]
end define; 

macro pickup(stick) begin
  sticks[stick] := TRUE;
end macro; 

macro putdown(stick) begin
  sticks[stick] := FALSE
end macro; 

\* cannot do putdown(left) || putdown(right); so this is a helper. 
\* remember the process variables are shadowed in macro 
macro putdown_both() begin 
  sticks[first] := FALSE  || sticks[second] := FALSE; 
end macro; 

\* implements either left handed or right handed philsopher 
procedure eat(first=0, second=0) begin 
  PickUpFirst:
    await StickAvailable(first); 
    pickup(first); 
  PickUpSecond:
    if StickAvailable(second) then 
      pickup(second);
    else
      putdown(first); 
      goto PickUpFirst 
    end if; 
  Eat:
    skip; 
  Finish:
    putdown_both(); 
  return;
end procedure; 

fair process philosopher \in 1..(NPhilosophers-1) 
variables 
  left = IF self > 1 THEN self-1 ELSE Len(sticks);
  right = self;   

begin
RHPhilsopher:   
  call eat(left, right); 
end process;  

fair process lh_philosopher \in {NPhilosophers} 
variables 
  left = IF self > 1 THEN self-1 ELSE Len(sticks);
  right = self;   

begin
LHPhilsopher:   
  call eat(right, left); 
end process; 


end algorithm; *) 


\* BEGIN TRANSLATION
\* Process variable left of process philosopher at line 69 col 3 changed to left_
\* Process variable right of process philosopher at line 70 col 3 changed to right_
VARIABLES sticks, pc, stack

(* define statement *)
StickAvailable(stick) == ~sticks[stick]

VARIABLES first, second, left_, right_, left, right

vars == << sticks, pc, stack, first, second, left_, right_, left, right >>

ProcSet == (1..(NPhilosophers-1)) \cup ({NPhilosophers})

Init == (* Global variables *)
        /\ sticks = [x \in 1..NPhilosophers |-> FALSE]
        (* Procedure eat *)
        /\ first = [ self \in ProcSet |-> 0]
        /\ second = [ self \in ProcSet |-> 0]
        (* Process philosopher *)
        /\ left_ = [self \in 1..(NPhilosophers-1) |-> IF self > 1 THEN self-1 ELSE Len(sticks)]
        /\ right_ = [self \in 1..(NPhilosophers-1) |-> self]
        (* Process lh_philosopher *)
        /\ left = [self \in {NPhilosophers} |-> IF self > 1 THEN self-1 ELSE Len(sticks)]
        /\ right = [self \in {NPhilosophers} |-> self]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..(NPhilosophers-1) -> "RHPhilsopher"
                                        [] self \in {NPhilosophers} -> "LHPhilsopher"]

PickUpFirst(self) == /\ pc[self] = "PickUpFirst"
                     /\ StickAvailable(first[self])
                     /\ sticks' = [sticks EXCEPT ![first[self]] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "PickUpSecond"]
                     /\ UNCHANGED << stack, first, second, left_, right_, left, 
                                     right >>

PickUpSecond(self) == /\ pc[self] = "PickUpSecond"
                      /\ IF StickAvailable(second[self])
                            THEN /\ sticks' = [sticks EXCEPT ![second[self]] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "Eat"]
                            ELSE /\ sticks' = [sticks EXCEPT ![first[self]] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "PickUpFirst"]
                      /\ UNCHANGED << stack, first, second, left_, right_, 
                                      left, right >>

Eat(self) == /\ pc[self] = "Eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Finish"]
             /\ UNCHANGED << sticks, stack, first, second, left_, right_, left, 
                             right >>

Finish(self) == /\ pc[self] = "Finish"
                /\ sticks' = [sticks EXCEPT ![first[self]] = FALSE,
                                            ![second[self]] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ first' = [first EXCEPT ![self] = Head(stack[self]).first]
                /\ second' = [second EXCEPT ![self] = Head(stack[self]).second]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << left_, right_, left, right >>

eat(self) == PickUpFirst(self) \/ PickUpSecond(self) \/ Eat(self)
                \/ Finish(self)

RHPhilsopher(self) == /\ pc[self] = "RHPhilsopher"
                      /\ /\ first' = [first EXCEPT ![self] = left_[self]]
                         /\ second' = [second EXCEPT ![self] = right_[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "eat",
                                                                  pc        |->  "Done",
                                                                  first     |->  first[self],
                                                                  second    |->  second[self] ] >>
                                                              \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "PickUpFirst"]
                      /\ UNCHANGED << sticks, left_, right_, left, right >>

philosopher(self) == RHPhilsopher(self)

LHPhilsopher(self) == /\ pc[self] = "LHPhilsopher"
                      /\ /\ first' = [first EXCEPT ![self] = right[self]]
                         /\ second' = [second EXCEPT ![self] = left[self]]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "eat",
                                                                  pc        |->  "Done",
                                                                  first     |->  first[self],
                                                                  second    |->  second[self] ] >>
                                                              \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "PickUpFirst"]
                      /\ UNCHANGED << sticks, left_, right_, left, right >>

lh_philosopher(self) == LHPhilsopher(self)

Next == (\E self \in ProcSet: eat(self))
           \/ (\E self \in 1..(NPhilosophers-1): philosopher(self))
           \/ (\E self \in {NPhilosophers}: lh_philosopher(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..(NPhilosophers-1) : WF_vars(philosopher(self)) /\ WF_vars(eat(self))
        /\ \A self \in {NPhilosophers} : WF_vars(lh_philosopher(self)) /\ WF_vars(eat(self))

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
\* Last modified Thu Aug 16 12:49:53 EDT 2018 by benjamin
\* Created Thu Aug 16 11:22:55 EDT 2018 by benjamin
