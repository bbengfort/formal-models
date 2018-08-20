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

\* when a message is read off the queue, this handles it but must be a proceedure not a macro  
\* proceedures can have local variables, args must have defaults, and must end with a return. 
procedure handle_message(val="")
variables 
  failed_message = "failed"
begin
  HandleValue: 
    either 
        \* Successful handling of value
        \* No label to prevent combinatorial explosion 
        return; 
    or 
      \* Failed handling of the value
      \* Label required to detect deadlock between reader and writer trying to write to queue
      \* Note that self refers to the process name; even in a macro
      ReadFailure: 
        \* If the queue is full the failure message is dropped 
        if Len(queue) < MaxQueueSize then 
          write_to_queue(self, val, FALSE);
        end if;  
        return; 
    end either; 
end procedure; 

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
  val = ""; 

begin
  Read:
    if Len(queue) > 0 then
      \* This is basically pop, Head gets the first item on the Queue, Tail is all elements but the first 
      val := Head(queue).message;
      queue := Tail(queue);
      
      \* Call must always be followed by a label
      \* we use a proceedure here to allow use of the same labels but from different processes  
      call handle_message(val);            
    end if; 
  EndRead:
    goto Read; 
end process; 

end algorithm; *) 

\* BEGIN TRANSLATION
\* Process variable val of process reader at line 64 col 3 changed to val_
VARIABLES queue, pc, stack

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLES val, failed_message, to_write, val_

vars == << queue, pc, stack, val, failed_message, to_write, val_ >>

ProcSet == {"writer"} \cup ({"r1", "r2"})

Init == (* Global variables *)
        /\ queue = <<>>
        (* Procedure handle_message *)
        /\ val = [ self \in ProcSet |-> ""]
        /\ failed_message = [ self \in ProcSet |-> "failed"]
        (* Process writer *)
        /\ to_write = "hi"
        (* Process reader *)
        /\ val_ = [self \in {"r1", "r2"} |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self \in {"r1", "r2"} -> "Read"]

HandleValue(self) == /\ pc[self] = "HandleValue"
                     /\ \/ /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ failed_message' = [failed_message EXCEPT ![self] = Head(stack[self]).failed_message]
                           /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        \/ /\ pc' = [pc EXCEPT ![self] = "ReadFailure"]
                           /\ UNCHANGED <<stack, val, failed_message>>
                     /\ UNCHANGED << queue, to_write, val_ >>

ReadFailure(self) == /\ pc[self] = "ReadFailure"
                     /\ IF Len(queue) < MaxQueueSize
                           THEN /\ Len(queue) < MaxQueueSize
                                /\ queue' = Append(queue, [writer |-> self, message |-> val[self], success |-> FALSE])
                           ELSE /\ TRUE
                                /\ queue' = queue
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ failed_message' = [failed_message EXCEPT ![self] = Head(stack[self]).failed_message]
                     /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << to_write, val_ >>

handle_message(self) == HandleValue(self) \/ ReadFailure(self)

Write == /\ pc["writer"] = "Write"
         /\ Len(queue) < MaxQueueSize
         /\ queue' = Append(queue, [writer |-> "writer", message |-> to_write, success |-> TRUE])
         /\ pc' = [pc EXCEPT !["writer"] = "Write"]
         /\ UNCHANGED << stack, val, failed_message, to_write, val_ >>

writer == Write

Read(self) == /\ pc[self] = "Read"
              /\ IF Len(queue) > 0
                    THEN /\ val_' = [val_ EXCEPT ![self] = Head(queue).message]
                         /\ queue' = Tail(queue)
                         /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "handle_message",
                                                                     pc        |->  "EndRead",
                                                                     failed_message |->  failed_message[self],
                                                                     val       |->  val[self] ] >>
                                                                 \o stack[self]]
                            /\ val' = [val EXCEPT ![self] = val_'[self]]
                         /\ failed_message' = [failed_message EXCEPT ![self] = "failed"]
                         /\ pc' = [pc EXCEPT ![self] = "HandleValue"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "EndRead"]
                         /\ UNCHANGED << queue, stack, val, failed_message, 
                                         val_ >>
              /\ UNCHANGED to_write

EndRead(self) == /\ pc[self] = "EndRead"
                 /\ pc' = [pc EXCEPT ![self] = "Read"]
                 /\ UNCHANGED << queue, stack, val, failed_message, to_write, 
                                 val_ >>

reader(self) == Read(self) \/ EndRead(self)

Next == writer
           \/ (\E self \in ProcSet: handle_message(self))
           \/ (\E self \in {"r1", "r2"}: reader(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Aug 15 12:13:44 EDT 2018 by benjamin
\* Created Wed Aug 15 10:51:54 EDT 2018 by benjamin
