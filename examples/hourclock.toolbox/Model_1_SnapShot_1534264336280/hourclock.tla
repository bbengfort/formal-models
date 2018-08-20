----------------------------- MODULE hourclock -----------------------------

EXTENDS Integers 

\* Define operators (like programming functions and can take parameters) 
HourRange == 1..12

(*--algorithm hourclock 

variables 
  hour \in HourRange; 
  pm \in {TRUE, FALSE}; \* BOOLEAN
  blinking = FALSE; 

define 
  \* convention is TypeOK; but this is a type invariant
  TypeInvariant  == 
    /\ hour \in HourRange
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
      
    either
      \* the power goes out 
      blinking := TRUE; 
      hour := 12; 
      pm := FALSE;      
    or 
      \* user resets the clock 
      with 
        new_hour \in HourRange, 
        new_pm \in BOOLEAN
      do 
        hour := new_hour; 
        pm := new_pm;
        blinking := FALSE;
      end with
    or 
      \* nothing happens 
      skip; 
    end either;  
    
  end while; 

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES hour, pm, blinking, pc

(* define statement *)
TypeInvariant  ==
  /\ hour \in HourRange
  /\ pm \in BOOLEAN


vars == << hour, pm, blinking, pc >>

Init == (* Global variables *)
        /\ hour \in HourRange
        /\ pm \in {TRUE, FALSE}
        /\ blinking = FALSE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF hour = 12
               THEN /\ hour' = 1
                    /\ pm' = ~pm
               ELSE /\ hour' = hour + 1
                    /\ pm' = pm
         /\ \/ /\ blinking' = TRUE
               /\ pc' = "Lbl_2"
            \/ /\ pc' = "Lbl_3"
               /\ UNCHANGED blinking
            \/ /\ TRUE
               /\ pc' = "Lbl_1"
               /\ UNCHANGED blinking

Lbl_2 == /\ pc = "Lbl_2"
         /\ hour' = 12
         /\ pm' = FALSE
         /\ pc' = "Lbl_1"
         /\ UNCHANGED blinking

Lbl_3 == /\ pc = "Lbl_3"
         /\ \E new_hour \in HourRange:
              \E new_pm \in BOOLEAN:
                /\ hour' = new_hour
                /\ pm' = new_pm
                /\ blinking' = FALSE
         /\ pc' = "Lbl_1"

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 12:32:06 EDT 2018 by benjamin
\* Created Tue Aug 14 12:06:14 EDT 2018 by benjamin
