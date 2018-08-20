------------------------------- MODULE bayou -------------------------------
(*
  A specification for anti-entropy syncrhonization that checks the liveness 
  property that servers become eventually consistent and the safety property 
  that clients receive only monotonically increasing version numbers.
  
  There are two types of processes in this model, clients and replicas. The 
  client process(es) send a finite number of messages to any server at each 
  timestep. Replicas respond with a monotonically increasing counter. 
  Periodically they synchronize to ensure that they are at the same counter.    
*)

EXTENDS TLC, Naturals, FiniteSets, Sequences 

\* There can be one or more clients and two or more replicas in the system.
\* Moreover, clients and replicas must have unique IDs to make the mailbox/
\* networking system work (usually {r1, r2} and {c1, c2}).  
CONSTANTS Clients, Replicas  
ASSUME Cardinality(Clients) > 0 /\ Cardinality(Replicas) > 1
ASSUME Clients \intersect Replicas = {}  

\* Every client sends a maximum number of messages before stopping. 
CONSTANT MaxRequestsPerClient 
ASSUME MaxRequestsPerClient \in Nat

RPC == {"request", "sync"}

(*--algorithm bayou 

\* Global variables that processes operate on 
variables   
  \* Replica state is a monotonically increasing counter. 
  counters = [r \in Replicas |-> 0];
  
  \* Mailboxes for each replica and client for sending and receiving.  
  messages = [n \in Replicas \union Clients |-> {}];  
  
define 
  \* Type checking for model behavior 
  TypeInvariant == 
    /\ counters \in [Replicas -> Nat]
           
  \* Eventual Consistency Liveness Property
  \* Eventually and for all time afterward, all replicas will have the same counter. 
  EventualConsistency == 
    <>[](\A r1, r2 \in Replicas: counters[r1] = counters[r2]) 
    
  \* Alternative definition of EC:
  \* There exists an i from 1 to max possible version where all replicas eventually 
  \* and for all time afterward have their counter set to i.  
  EventualConsistency2 == 
    \E i \in 1..(Cardinality(Clients) * MaxRequestsPerClient):
      <>[](\A r \in Replicas: counters[r] = i)
end define; 

fair process replica \in Replicas begin
Serve:
  either 
    \* Send a synchronization message to another replica 
    with peer \in {r \in Replicas: r # self} do 
      skip; 
    end with; 
  or 
    \* Handle a message that has come in on the network
    \* Note that with t \in {} blocks until set is not empty (e.g. await set not empty). 
    with msg \in messages[self] do 
      skip;
    end with; 
  end either;  
end process; 

fair process client \in Clients 
variables 
  reqs = 0; 
  
begin
  Request:  
    \* Make a fixed number of requests  
    while reqs < MaxRequestsPerClient do 
      \* send a request to the server and await a response.  
      Response:
        \* await a response from the server  
        skip; 
      reqs := reqs + 1; 
    end while; 
end process; 

end algorithm; *)  
\* BEGIN TRANSLATION
VARIABLES counters, messages, pc

(* define statement *)
TypeInvariant ==
  /\ counters \in [Replicas -> Nat]



EventualConsistency ==
  <>[](\A r1, r2 \in Replicas: counters[r1] = counters[r2])




EventualConsistency2 ==
  \E i \in 1..(Cardinality(Clients) * MaxRequestsPerClient):
    <>[](\A r \in Replicas: counters[r] = i)

VARIABLE reqs

vars == << counters, messages, pc, reqs >>

ProcSet == (Replicas) \cup (Clients)

Init == (* Global variables *)
        /\ counters = [r \in Replicas |-> 0]
        /\ messages = [n \in Replicas \union Clients |-> {}]
        (* Process client *)
        /\ reqs = [self \in Clients |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Replicas -> "Serve"
                                        [] self \in Clients -> "Request"]

Serve(self) == /\ pc[self] = "Serve"
               /\ \/ /\ \E peer \in {r \in Replicas: r # self}:
                          TRUE
                  \/ /\ \E msg \in messages[self]:
                          TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << counters, messages, reqs >>

replica(self) == Serve(self)

Request(self) == /\ pc[self] = "Request"
                 /\ IF reqs[self] < MaxRequestsPerClient
                       THEN /\ pc' = [pc EXCEPT ![self] = "Response"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << counters, messages, reqs >>

Response(self) == /\ pc[self] = "Response"
                  /\ TRUE
                  /\ reqs' = [reqs EXCEPT ![self] = reqs[self] + 1]
                  /\ pc' = [pc EXCEPT ![self] = "Request"]
                  /\ UNCHANGED << counters, messages >>

client(self) == Request(self) \/ Response(self)

Next == (\E self \in Replicas: replica(self))
           \/ (\E self \in Clients: client(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Replicas : WF_vars(replica(self))
        /\ \A self \in Clients : WF_vars(client(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Aug 16 16:38:51 CDT 2018 by benjamin
\* Created Thu Aug 16 15:47:07 CDT 2018 by benjamin
