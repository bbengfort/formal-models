-------------------------------- MODULE max --------------------------------

EXTENDS Integers, TLC, Sequences

\* Definition of Max 
Max(seq) == 
  LET 
    setmax(set) == CHOOSE x \in set: \A y \in set: x >= y \* definition of set max 
    seq2set == {seq[x] : x \in 1..Len(seq)}               \* convert sequence to a set 
  IN 
    \* get the max of the set of the sequence
    setmax(seq2set) 

\* Algorithm that computes max to compare to definition of Max 
(*--algorithm max 

variables
  \* Input is the 4-tuple of cross product sets -5 to 5
  \* input \in (-5..5) \X (-5..5) \X (-5..5) \X (-5..5);
  
  \* Input is a sequence of any length, L with ints -5 to 5 
  L \in 1..4;
  input \in [1..L -> (-5..5)]; 
  
  max = input[1]; \* max is set to the first element in the input
  i = 1;          \* index counter for the while loop   
  
begin
  \* execute max algorithm 
  while i <= L do 
    if input[i] > max then 
      max := input[i];
    end if; 
    i := i+1;
  end while;
  
  \* define some success condition 
  assert max = Max(input); 

end algorithm; *)


\* BEGIN TRANSLATION
VARIABLES L, input, max, i, pc

vars == << L, input, max, i, pc >>

Init == (* Global variables *)
        /\ L \in 1..4
        /\ input \in [1..L -> (-5..5)]
        /\ max = input[1]
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i <= 4
               THEN /\ IF input[i] > max
                          THEN /\ max' = input[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ i' = i+1
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(max = Max(input), 
                              "Failure of assertion at line 36, column 3.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << max, i >>
         /\ UNCHANGED << L, input >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Aug 14 15:34:17 EDT 2018 by benjamin
\* Created Tue Aug 14 14:58:21 EDT 2018 by benjamin
