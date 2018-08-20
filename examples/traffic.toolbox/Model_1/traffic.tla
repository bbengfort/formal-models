------------------------------ MODULE traffic ------------------------------

(*--algorithm traffic 
variables 
  at_light = TRUE; 
  light = "green"; 

define 
  Liveness == (light = "red") ~> (light = "green") 
end define; 

fair process traffic_light = "light" begin
Cycle:
  while at_light do 
    if light = "red" then 
      light := "green"; 
    else
      light := "red";
    end if; 
  end while;    
end process; 

fair+ process car = "car" begin
Car:
  await light = "green"; 
  at_light := FALSE; 
end process;

end algorithm; *)

 
\* BEGIN TRANSLATION
VARIABLES at_light, light, pc

(* define statement *)
Liveness == (light = "red") ~> (light = "green")


vars == << at_light, light, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "green"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Car"]

Cycle == /\ pc["light"] = "Cycle"
         /\ IF at_light
               THEN /\ IF light = "red"
                          THEN /\ light' = "green"
                          ELSE /\ light' = "red"
                    /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
               ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
                    /\ light' = light
         /\ UNCHANGED at_light

traffic_light == Cycle

Car == /\ pc["car"] = "Car"
       /\ light = "green"
       /\ at_light' = FALSE
       /\ pc' = [pc EXCEPT !["car"] = "Done"]
       /\ light' = light

car == Car

Next == traffic_light \/ car
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(traffic_light)
        /\ SF_vars(car)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Aug 15 15:34:53 EDT 2018 by benjamin
\* Created Wed Aug 15 15:03:11 EDT 2018 by benjamin
