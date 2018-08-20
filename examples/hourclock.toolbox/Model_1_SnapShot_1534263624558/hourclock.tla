----------------------------- MODULE hourclock -----------------------------

EXTENDS Integers 

(*--algorithm hourclock 

variables 
  hour \in 1..12; 
  pm \in {TRUE, FALSE}; \* BOOLEAN

define 
  \* convention is TypeOK; but this is a type invariant
  TypeInvariant  == 
    /\ hour \in 1..12
    /\ pm \in BOOLEAN 
end define; 

begin
  \* Run while loop forever. 
  while TRUE do 
    if hour = 12 then 
      hour := 1; 
      pm := ~pm; 
    else 
      hour := hour + 1; 
    end if;  
  end while; 

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES hour, pm

(* define statement *)
TypeInvariant  ==
  /\ hour \in 1..12
  /\ pm \in BOOLEAN


vars == << hour, pm >>

Init == (* Global variables *)
        /\ hour \in 1..12
        /\ pm \in {TRUE, FALSE}

Next == IF hour = 12
           THEN /\ hour' = 1
                /\ pm' = ~pm
           ELSE /\ hour' = hour + 1
                /\ pm' = pm

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 12:20:15 EDT 2018 by benjamin
\* Created Tue Aug 14 12:06:14 EDT 2018 by benjamin
