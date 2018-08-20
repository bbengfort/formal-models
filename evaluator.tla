----------------------------- MODULE evaluator -----------------------------

EXTENDS Integers, Sequences

\* Get the first index of the element in the sequence or barf 
FirstIndexOf(elem, sequence) == 
  CHOOSE i \in 1..Len(sequence):
    sequence[i] = elem 
  

\* Get all values of sequence, struct, or func (e.g. Range)  
Values(f) == { f[x]: x \in DOMAIN f }

\* TRUE if at least one element in the set is positive, else FALSE
AtLeastOnePositive(set) == 
  \E x \in set: x > 0
  
\* TRUE if all elements in the set are positive, else FALSE
AllPositive(set) == 
  \A x \in set: x > 0  

\* Return an arbitrary positive element (always the same choice)
\* Raises an error if no element exists in the set   
APositive(set) == 
  CHOOSE x \in set: x > 0 

\* Define the maximum value of the set
\* Assume set is nonempty  
Max(set) == 
  CHOOSE x \in set: 
    \A y \in set:
      x >= y  
      
Max2(set) == 
  CHOOSE x \in set:
    \A y \in (set \ {x}):
      x > y
      
      
IsPrime(x) == 
  \* Remember, 1 is not a prime
  ~ \E y \in 2..(x-1): 
    x % y = 0  
    
PrimesLessThan(x) == 
  {y \in 2..(x-1): IsPrime(y)} 
  
  
\* Structures (equivalent to a map) 
s == [a |-> "b", hello |-> "c"]

\* Functions are a mapping of domain to range  
f == [x \in 1..5 |-> 2*x]

\* Returns the domain of the function 
d == DOMAIN f 


FuncSets == [1..4 -> 1..4] 

Symmetric == 
  CHOOSE g \in FuncSets:
    /\ g[1] = 3 
    /\ \A x \in 1..4:
        g[g[x]] = x

=============================================================================
\* Modification History
\* Last modified Thu Aug 16 12:39:28 EDT 2018 by benjamin
\* Created Tue Aug 14 13:00:57 EDT 2018 by benjamin
