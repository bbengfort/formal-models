---------------------------- MODULE readerwriter ----------------------------
(*
  Reader-Writer demonstrates a specification that allows a writer to write 
  messages to a bounded queue and has a reader that reads off the queue. 
*)
EXTENDS TLC, Integers, Sequences 

\* Model constants for reader writer 
CONSTANT MaxQueueSize 

(*--algorithm reader 
variables
  \* message queue that writers writes to and reader reads from 
  queue = <<>>; 

define 
  \* BoundedQueue invariant ensures that the writer blocks if the queue is full. 
  BoundedQueue == Len(queue) <= MaxQueueSize
end define; 


macro write_to_queue(val) begin 
  await Len(queue) < MaxQueueSize;  
  queue := Append(queue, val);
end macro;

process writer = "writer"
variables 
  to_write = "hi"; 
begin 
  Write:
    write_to_queue(to_write); 
    goto Write;  
end process; 


process reader = "reader" 
variables 
  val = "none"; 

begin
  Read:
    if Len(queue) > 0 then
      val := Head(queue);
      queue := Tail(queue);
    end if; 
    goto Read; 
end process; 

end algorithm; *) 

\* BEGIN TRANSLATION
VARIABLES queue, pc

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLES to_write, val

vars == << queue, pc, to_write, val >>

ProcSet == {"writer"} \cup {"reader"}

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process writer *)
        /\ to_write = "hi"
        (* Process reader *)
        /\ val = "none"
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self = "reader" -> "Read"]

Write == /\ pc["writer"] = "Write"
         /\ Len(queue) < MaxQueueSize
         /\ queue' = Append(queue, to_write)
         /\ pc' = [pc EXCEPT !["writer"] = "Write"]
         /\ UNCHANGED << to_write, val >>

writer == Write

Read == /\ pc["reader"] = "Read"
        /\ IF Len(queue) > 0
              THEN /\ val' = Head(queue)
                   /\ queue' = Tail(queue)
              ELSE /\ TRUE
                   /\ UNCHANGED << queue, val >>
        /\ pc' = [pc EXCEPT !["reader"] = "Read"]
        /\ UNCHANGED to_write

reader == Read

Next == writer \/ reader
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Aug 15 11:24:14 EDT 2018 by benjamin
\* Created Wed Aug 15 10:51:54 EDT 2018 by benjamin
