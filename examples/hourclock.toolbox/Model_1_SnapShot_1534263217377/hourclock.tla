----------------------------- MODULE hourclock -----------------------------

EXTENDS Integers 

(*--algorithm hourclock 

variables 
  hour \in 1..12; 

define 
  \* convention is TypeOK; but this is a type invariant
  TypeInvariant  == 
    /\ hour \in 1..12
end define; 

begin
  \* Run while loop forever. 
  while TRUE do 
    if hour = 12 then 
      hour := 1; 
    else 
      hour := hour + 1; 
    end if;  
  end while; 

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLE hour

(* define statement *)
TypeInvariant  ==
  /\ hour \in 1..12


vars == << hour >>

Init == (* Global variables *)
        /\ hour \in 1..12

Next == IF hour = 12
           THEN /\ hour' = 1
           ELSE /\ hour' = hour + 1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 12:13:25 EDT 2018 by benjamin
\* Created Tue Aug 14 12:06:14 EDT 2018 by benjamin
