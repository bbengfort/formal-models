------------------------------ MODULE rollout ------------------------------

EXTENDS TLC, Integers, Sequences, FiniteSets 

CONSTANTS Servers 
ASSUME Cardinality(Servers) > 1 

\* A server can either be ready or upgrading/down 
Status == {"ready", "upgrading"} 

(*--algorithm rollout 
variables
  version = [s \in Servers |-> 0];       \* All servers start at version 0 
  status = [s \in Servers |-> "ready"];  \* All servers start at ready 
  load_balancer = Servers;               \* Set of servers that can be accessed by clients 
  
define
  \* Ensure that servers have the correct version and status 
  TypeInvariant == 
    /\ version \in [Servers -> {0, 1}] 
    /\ status \in [Servers -> Status]
  
  \* There is at least one server in the load_balancer and all servers in lb are ready
  Availability == 
    /\ load_balancer # {}
    /\ \A s \in load_balancer: status[s] = "ready"
    
  \* All servers in the load balancer must have the same version 
  VersionConsistency == 
    \A s1, s2 \in load_balancer: version[s1] = version[s2]   
end define; 

\* A coordinator process that decides which servers to update and when. 
\* The current algorithm updates one first, then the rest. 
fair process manager = "manager"
variables 
  first \in Servers 

begin 
  UpdateFirst:
    \* remove the server from the load balancer and tell it to upgrade  
    load_balancer := load_balancer \ {first};
    status[first] := "upgrading"; 
  ReturnFirst:
    await status[first] = "ready"; 
    load_balancer := load_balancer \union {first};
end process; 

process server \in Servers 
begin
  Upgrade:
    await status[self] = "upgrading";
    version[self] := 1; 
    status[self] := "ready";   
end process; 

end algorithm; *) 
\* BEGIN TRANSLATION
VARIABLES version, status, load_balancer, pc

(* define statement *)
TypeInvariant ==
  /\ version \in [Servers -> {0, 1}]
  /\ status \in [Servers -> Status]


Availability ==
  /\ load_balancer # {}
  /\ \A s \in load_balancer: status[s] = "ready"


VersionConsistency ==
  \A s1, s2 \in load_balancer: version[s1] = version[s2]

VARIABLE first

vars == << version, status, load_balancer, pc, first >>

ProcSet == {"manager"} \cup (Servers)

Init == (* Global variables *)
        /\ version = [s \in Servers |-> 0]
        /\ status = [s \in Servers |-> "ready"]
        /\ load_balancer = Servers
        (* Process manager *)
        /\ first \in Servers
        /\ pc = [self \in ProcSet |-> CASE self = "manager" -> "UpdateFirst"
                                        [] self \in Servers -> "Upgrade"]

UpdateFirst == /\ pc["manager"] = "UpdateFirst"
               /\ load_balancer' = load_balancer \ {first}
               /\ status' = [status EXCEPT ![first] = "upgrading"]
               /\ pc' = [pc EXCEPT !["manager"] = "ReturnFirst"]
               /\ UNCHANGED << version, first >>

ReturnFirst == /\ pc["manager"] = "ReturnFirst"
               /\ status[first] = "ready"
               /\ load_balancer' = (load_balancer \union {first})
               /\ pc' = [pc EXCEPT !["manager"] = "Done"]
               /\ UNCHANGED << version, status, first >>

manager == UpdateFirst \/ ReturnFirst

Upgrade(self) == /\ pc[self] = "Upgrade"
                 /\ status[self] = "upgrading"
                 /\ version' = [version EXCEPT ![self] = 1]
                 /\ status' = [status EXCEPT ![self] = "ready"]
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << load_balancer, first >>

server(self) == Upgrade(self)

Next == manager
           \/ (\E self \in Servers: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(manager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Aug 16 14:02:27 EDT 2018 by benjamin
\* Created Thu Aug 16 13:42:49 EDT 2018 by benjamin
