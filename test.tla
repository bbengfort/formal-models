-------------------------------- MODULE test --------------------------------

(*--algorithm test 

variables 
  foo = 0 

begin
  skip;

end algorithm; *) 
\* BEGIN TRANSLATION
VARIABLES foo, pc

vars == << foo, pc >>

Init == (* Global variables *)
        /\ foo = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ foo' = foo

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Aug 16 16:37:45 CDT 2018 by benjamin
\* Created Thu Aug 16 16:36:12 CDT 2018 by benjamin
