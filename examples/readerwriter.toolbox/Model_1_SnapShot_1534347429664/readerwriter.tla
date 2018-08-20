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

\* allows a process to append a value to a FIFO queue but blocks until the queue has capacity 
macro write_to_queue(writer, message, success) begin 
  await Len(queue) < MaxQueueSize;  
  queue := Append(queue, [writer |-> writer, message |-> message, success |-> success]);
end macro;

\* writer process adds values to the queue and blocks if queue is full 
process writer = "writer"
variables 
  to_write = "hi"; 
begin 
  Write:
    write_to_queue("writer", to_write, TRUE); 
    goto Write;  
end process; 

\* reader process pops values off the queue but doesn't block if queue is empty 
process reader = "reader" 
variables 
  val = "none"; 

begin
  Read:
    if Len(queue) > 0 then
      val := Head(queue);
      queue := Tail(queue);
        
       HandleValue: 
        either 
          \* Successful handling of value 
          skip; 
        or 
          \* Failed handling of the value
          write_to_queue("reader", val, FALSE); 
          val := "none"; 
        end either;       
    end if; 
  EndRead:
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
         /\ queue' = Append(queue, [writer |-> "writer", message |-> to_write, success |-> TRUE])
         /\ pc' = [pc EXCEPT !["writer"] = "Write"]
         /\ UNCHANGED << to_write, val >>

writer == Write

Read == /\ pc["reader"] = "Read"
        /\ IF Len(queue) > 0
              THEN /\ val' = Head(queue)
                   /\ queue' = Tail(queue)
                   /\ pc' = [pc EXCEPT !["reader"] = "HandleValue"]
              ELSE /\ pc' = [pc EXCEPT !["reader"] = "EndRead"]
                   /\ UNCHANGED << queue, val >>
        /\ UNCHANGED to_write

HandleValue == /\ pc["reader"] = "HandleValue"
               /\ \/ /\ TRUE
                     /\ UNCHANGED <<queue, val>>
                  \/ /\ Len(queue) < MaxQueueSize
                     /\ queue' = Append(queue, [writer |-> "reader", message |-> val, success |-> FALSE])
                     /\ val' = "none"
               /\ pc' = [pc EXCEPT !["reader"] = "EndRead"]
               /\ UNCHANGED to_write

EndRead == /\ pc["reader"] = "EndRead"
           /\ pc' = [pc EXCEPT !["reader"] = "Read"]
           /\ UNCHANGED << queue, to_write, val >>

reader == Read \/ HandleValue \/ EndRead

Next == writer \/ reader
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Aug 15 11:36:57 EDT 2018 by benjamin
\* Created Wed Aug 15 10:51:54 EDT 2018 by benjamin
