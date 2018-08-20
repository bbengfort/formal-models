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
    hour := hour + 1;
    if hour > 12 then 
      hour := 1;
    end if;  
  end while; 

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES hour, pc

(* define statement *)
TypeInvariant  ==
  /\ hour \in 1..12


vars == << hour, pc >>

Init == (* Global variables *)
        /\ hour \in 1..12
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ hour' = hour + 1
         /\ IF hour' > 12
               THEN /\ pc' = "Lbl_2"
               ELSE /\ pc' = "Lbl_1"

Lbl_2 == /\ pc = "Lbl_2"
         /\ hour' = 1
         /\ pc' = "Lbl_1"

Next == Lbl_1 \/ Lbl_2

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 12:11:29 EDT 2018 by benjamin
\* Created Tue Aug 14 12:06:14 EDT 2018 by benjamin
