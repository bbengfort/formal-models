--------------------------- MODULE bounded_buffer ---------------------------

(*
  This was a challenge posed to extreme programming that took the fastest person 
  16 hours to solve with unittesting. We solved it in about an hour with the 
  formal specification. 
  
  http://wiki.c2.com/?ExtremeProgrammingChallengeFourteen
*)


EXTENDS TLC, Integers, Sequences 
CONSTANT MaxBuffer, Writers, Readers  

(*--algorithm bounded_buffer 

variables 
  occupied = 0; 
  awake = Writers \union Readers;
  sleeping = {};  
  
define 
  AllThreadsStatus ==
    awake \union sleeping = Writers \union Readers
  OccupiedCorrect == 
    /\ occupied >= 0 
    /\ occupied <= MaxBuffer  
end define;
   
macro notify() begin
  if ~ sleeping = {} then
    with t \in sleeping do  
      awake := awake \union {t};  \* add the thread to awake 
\*      sleeping := sleeping \ {t}; \* remove the thread from sleeping
    end with; 
  end if;  
end macro;

macro sleep() begin 
  awake := awake \ {self};            \* remove self from awake 
\*  sleeping := sleeping \union {self}; \* add self to sleeping
end macro;

process writer \in Writers begin

Write:
  while occupied = MaxBuffer do 
    sleep();
    WriteSleep:
      await self \in awake    
  end while; 
  
  notify();
  occupied := occupied + 1;  
  goto Write;
end process 

process reader \in Readers begin 
  
Read: 
  while occupied = 0 do 
    sleep();
    ReadSleep:
      await self \in awake
  end while; 
  notify();
  occupied := occupied - 1;
  goto Read;
end process
 

end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES occupied, awake, sleeping, pc

(* define statement *)
AllThreadsStatus ==
  awake \union sleeping = Writers \union Readers
OccupiedCorrect ==
  /\ occupied >= 0
  /\ occupied <= MaxBuffer


vars == << occupied, awake, sleeping, pc >>

ProcSet == (Writers) \cup (Readers)

Init == (* Global variables *)
        /\ occupied = 0
        /\ awake = (Writers \union Readers)
        /\ sleeping = {}
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "Write"
                                        [] self \in Readers -> "Read"]

Write(self) == /\ pc[self] = "Write"
               /\ IF occupied = MaxBuffer
                     THEN /\ awake' = awake \ {self}
                          /\ pc' = [pc EXCEPT ![self] = "WriteSleep"]
                          /\ UNCHANGED occupied
                     ELSE /\ IF ~ sleeping = {}
                                THEN /\ \E t \in sleeping:
                                          awake' = (awake \union {t})
                                ELSE /\ TRUE
                                     /\ awake' = awake
                          /\ occupied' = occupied + 1
                          /\ pc' = [pc EXCEPT ![self] = "Write"]
               /\ UNCHANGED sleeping

WriteSleep(self) == /\ pc[self] = "WriteSleep"
                    /\ self \in awake
                    /\ pc' = [pc EXCEPT ![self] = "Write"]
                    /\ UNCHANGED << occupied, awake, sleeping >>

writer(self) == Write(self) \/ WriteSleep(self)

Read(self) == /\ pc[self] = "Read"
              /\ IF occupied = 0
                    THEN /\ awake' = awake \ {self}
                         /\ pc' = [pc EXCEPT ![self] = "ReadSleep"]
                         /\ UNCHANGED occupied
                    ELSE /\ IF ~ sleeping = {}
                               THEN /\ \E t \in sleeping:
                                         awake' = (awake \union {t})
                               ELSE /\ TRUE
                                    /\ awake' = awake
                         /\ occupied' = occupied - 1
                         /\ pc' = [pc EXCEPT ![self] = "Read"]
              /\ UNCHANGED sleeping

ReadSleep(self) == /\ pc[self] = "ReadSleep"
                   /\ self \in awake
                   /\ pc' = [pc EXCEPT ![self] = "Read"]
                   /\ UNCHANGED << occupied, awake, sleeping >>

reader(self) == Read(self) \/ ReadSleep(self)

Next == (\E self \in Writers: writer(self))
           \/ (\E self \in Readers: reader(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Aug 15 13:53:43 EDT 2018 by benjamin
\* Created Wed Aug 15 12:32:40 EDT 2018 by benjamin
