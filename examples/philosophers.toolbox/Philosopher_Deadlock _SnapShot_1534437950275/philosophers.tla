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
   
  \* left and right are global variables that are assigned in each process. 
  left = 0; 
  right = 0;

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
  sticks[left] := FALSE  || sticks[right] := FALSE; 
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
 
     

begin
RHPhilsopher:
  left := IF self > 1 THEN self-1 ELSE Len(sticks);
  right := self; 
  call eat(left, right); 
end process;  

fair process lh_philosopher \in {NPhilosophers}  
    

begin
LHPhilsopher: 
  left := IF self > 1 THEN self-1 ELSE Len(sticks);
  right := self;   
  call eat(right, left); 
end process; 


end algorithm; *) 


\* BEGIN TRANSLATION
VARIABLES sticks, left, right, pc, stack

(* define statement *)
StickAvailable(stick) == ~sticks[stick]

VARIABLES first, second

vars == << sticks, left, right, pc, stack, first, second >>

ProcSet == (1..(NPhilosophers-1)) \cup ({NPhilosophers})

Init == (* Global variables *)
        /\ sticks = [x \in 1..NPhilosophers |-> FALSE]
        /\ left = 0
        /\ right = 0
        (* Procedure eat *)
        /\ first = [ self \in ProcSet |-> 0]
        /\ second = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..(NPhilosophers-1) -> "RHPhilsopher"
                                        [] self \in {NPhilosophers} -> "LHPhilsopher"]

PickUpFirst(self) == /\ pc[self] = "PickUpFirst"
                     /\ StickAvailable(first[self])
                     /\ sticks' = [sticks EXCEPT ![first[self]] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = "PickUpSecond"]
                     /\ UNCHANGED << left, right, stack, first, second >>

PickUpSecond(self) == /\ pc[self] = "PickUpSecond"
                      /\ IF StickAvailable(second[self])
                            THEN /\ sticks' = [sticks EXCEPT ![second[self]] = TRUE]
                                 /\ pc' = [pc EXCEPT ![self] = "Eat"]
                            ELSE /\ sticks' = [sticks EXCEPT ![first[self]] = FALSE]
                                 /\ pc' = [pc EXCEPT ![self] = "PickUpFirst"]
                      /\ UNCHANGED << left, right, stack, first, second >>

Eat(self) == /\ pc[self] = "Eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Finish"]
             /\ UNCHANGED << sticks, left, right, stack, first, second >>

Finish(self) == /\ pc[self] = "Finish"
                /\ sticks' = [sticks EXCEPT ![left] = FALSE,
                                            ![right] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ first' = [first EXCEPT ![self] = Head(stack[self]).first]
                /\ second' = [second EXCEPT ![self] = Head(stack[self]).second]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << left, right >>

eat(self) == PickUpFirst(self) \/ PickUpSecond(self) \/ Eat(self)
                \/ Finish(self)

RHPhilsopher(self) == /\ pc[self] = "RHPhilsopher"
                      /\ left' = (IF self > 1 THEN self-1 ELSE Len(sticks))
                      /\ right' = self
                      /\ /\ first' = [first EXCEPT ![self] = left']
                         /\ second' = [second EXCEPT ![self] = right']
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "eat",
                                                                  pc        |->  "Done",
                                                                  first     |->  first[self],
                                                                  second    |->  second[self] ] >>
                                                              \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "PickUpFirst"]
                      /\ UNCHANGED sticks

philosopher(self) == RHPhilsopher(self)

LHPhilsopher(self) == /\ pc[self] = "LHPhilsopher"
                      /\ left' = (IF self > 1 THEN self-1 ELSE Len(sticks))
                      /\ right' = self
                      /\ /\ first' = [first EXCEPT ![self] = right']
                         /\ second' = [second EXCEPT ![self] = left']
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "eat",
                                                                  pc        |->  "Done",
                                                                  first     |->  first[self],
                                                                  second    |->  second[self] ] >>
                                                              \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "PickUpFirst"]
                      /\ UNCHANGED sticks

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
\* Last modified Thu Aug 16 12:45:43 EDT 2018 by benjamin
\* Created Thu Aug 16 11:22:55 EDT 2018 by benjamin
