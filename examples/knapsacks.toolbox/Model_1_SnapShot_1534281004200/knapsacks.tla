----------------------------- MODULE knapsacks -----------------------------

EXTENDS Integers, TLC, Sequences, Reduce


\* Create items for the knapsack (all should be constants) 
Items == {"a", "b", "c"} 

SizeRange == 1..3 
ValueRange == 0..2 
Capacity == 7 

\* This is what an itemset looks like 
HardcodedItemSet == [
  a |-> [size |-> 1, value |-> 1], 
  b |-> [size |-> 2, value |-> 3],
  c |-> [size |-> 3, value |-> 1] 
]

\* Item definition 
itemset == HardcodedItemSet 

\* Helper functions for items 
ValueOf(name) == itemset[name].value 
SizeOf(name) == itemset[name].size

\* Knapsack Definition 
PossibleKnapsacks == [Items -> 0..5]
 
SizeOfKnapsack(k) ==
  k.a * SizeOf("a") + 
  k.b * SizeOf("b") + 
  k.c * SizeOf("c")
  
ValueOfKnapsack(k) ==
  k.a * ValueOf("a") + 
  k.b * ValueOf("b") + 
  k.c * ValueOf("c") 
  
 
 ValidKnapsacks == {k \in PossibleKnapsacks: SizeOfKnapsack(k) <= Capacity}
 BestKnapsack == 
  CHOOSE k \in ValidKnapsacks:
    \A k2 \in ValidKnapsacks \ {k}:
      ValueOfKnapsack(k) >= ValueOfKnapsack(k2) 

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 17:09:59 EDT 2018 by benjamin
\* Created Tue Aug 14 16:27:17 EDT 2018 by benjamin
