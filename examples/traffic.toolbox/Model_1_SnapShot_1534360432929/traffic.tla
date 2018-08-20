------------------------------ MODULE traffic ------------------------------

(*--algorithm traffic 
variables 
  at_light = TRUE; 
  light = "green"; 

define 
  Liveness == <>(~at_light) 
end define; 

process traffic_light = "light" begin
Cycle:
  while TRUE do 
    if light = "red" then 
      light := "green"; 
    else
      light := "red";
    end if; 
  end while;    
end process; 

fair process car = "car" begin
Car:
  await light = "green"; 
  at_light := FALSE; 
end process;

end algorithm; *)

 
\* BEGIN TRANSLATION
VARIABLES at_light, light, pc

(* define statement *)
Liveness == <>(~at_light)


vars == << at_light, light, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "green"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Car"]

Cycle == /\ pc["light"] = "Cycle"
         /\ IF light = "red"
               THEN /\ light' = "green"
               ELSE /\ light' = "red"
         /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
         /\ UNCHANGED at_light

traffic_light == Cycle

Car == /\ pc["car"] = "Car"
       /\ light = "green"
       /\ at_light' = FALSE
       /\ pc' = [pc EXCEPT !["car"] = "Done"]
       /\ light' = light

car == Car

Next == traffic_light \/ car

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(car)

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Wed Aug 15 15:13:48 EDT 2018 by benjamin
\* Created Wed Aug 15 15:03:11 EDT 2018 by benjamin
