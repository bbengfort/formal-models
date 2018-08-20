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
process reader \in {"r1", "r2"}  
variables 
  val = "none"; 

begin
  Read:
    if Len(queue) > 0 then
      \* This is basically pop, Head gets the first item on the Queue, Tail is all elements but the first 
      val := Head(queue).message;
      queue := Tail(queue);
        
       HandleValue: 
        either 
            \* Successful handling of value
            \* No label to prevent combinatorial explosion 
            skip; 
        or 
          \* Failed handling of the value
          \* Label required to detect deadlock between reader and writer trying to write to queue
          \* Note that self refers to the process name; even in a macro
          ReadFailure: 
            write_to_queue(self, val, FALSE); 
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

ProcSet == {"writer"} \cup ({"r1", "r2"})

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process writer *)
        /\ to_write = "hi"
        (* Process reader *)
        /\ val = [self \in {"r1", "r2"} |-> "none"]
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self \in {"r1", "r2"} -> "Read"]

Write == /\ pc["writer"] = "Write"
         /\ Len(queue) < MaxQueueSize
         /\ queue' = Append(queue, [writer |-> "writer", message |-> to_write, success |-> TRUE])
         /\ pc' = [pc EXCEPT !["writer"] = "Write"]
         /\ UNCHANGED << to_write, val >>

writer == Write

Read(self) == /\ pc[self] = "Read"
              /\ IF Len(queue) > 0
                    THEN /\ val' = [val EXCEPT ![self] = Head(queue).message]
                         /\ queue' = Tail(queue)
                         /\ pc' = [pc EXCEPT ![self] = "HandleValue"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "EndRead"]
                         /\ UNCHANGED << queue, val >>
              /\ UNCHANGED to_write

HandleValue(self) == /\ pc[self] = "HandleValue"
                     /\ \/ /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "EndRead"]
                        \/ /\ pc' = [pc EXCEPT ![self] = "ReadFailure"]
                     /\ UNCHANGED << queue, to_write, val >>

ReadFailure(self) == /\ pc[self] = "ReadFailure"
                     /\ Len(queue) < MaxQueueSize
                     /\ queue' = Append(queue, [writer |-> self, message |-> val[self], success |-> FALSE])
                     /\ val' = [val EXCEPT ![self] = "none"]
                     /\ pc' = [pc EXCEPT ![self] = "EndRead"]
                     /\ UNCHANGED to_write

EndRead(self) == /\ pc[self] = "EndRead"
                 /\ pc' = [pc EXCEPT ![self] = "Read"]
                 /\ UNCHANGED << queue, to_write, val >>

reader(self) == Read(self) \/ HandleValue(self) \/ ReadFailure(self)
                   \/ EndRead(self)

Next == writer
           \/ (\E self \in {"r1", "r2"}: reader(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Aug 15 11:59:31 EDT 2018 by benjamin
\* Created Wed Aug 15 10:51:54 EDT 2018 by benjamin
