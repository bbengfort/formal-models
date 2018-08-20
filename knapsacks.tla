----------------------------- MODULE knapsacks -----------------------------

EXTENDS Integers, TLC, Sequences, Reduce

\* Use symmetric set with items in model to reduce checking time. 
CONSTANT Items  

SizeRange == 1..3 
ValueRange == 0..2 
Capacity == 7 

\* This is what an itemset looks like 
HardcodedItemSet == [
  a |-> [size |-> 1, value |-> 1], 
  b |-> [size |-> 2, value |-> 3],
  c |-> [size |-> 3, value |-> 1] 
]

\* This is all possible item sets 
ItemSet == [Items -> [size: SizeRange, value: ValueRange]]


\* Helper functions for itemsets 
ValueOf(name, itemset) == itemset[name].value 
SizeOf(name, itemset) == itemset[name].size

\* Knapsack Definition 
PossibleKnapsacks == [Items -> 0..5]
 
SizeOfKnapsack(k, itemset) ==
  LET 
    KnapsackSizeForItem(item) == k[item] * SizeOf(item, itemset)
  IN 
    ReduceSet(LAMBDA item, acc: KnapsackSizeForItem(item) + acc, DOMAIN k, 0) 
  
ValueOfKnapsack(k, itemset) ==
  LET 
    KnapsackValueForItem(item) == k[item] * ValueOf(item, itemset)
  IN 
    ReduceSet(LAMBDA item, acc: KnapsackValueForItem(item) + acc, DOMAIN k, 0)
  
 
ValidKnapsacks(itemset) == {k \in PossibleKnapsacks: SizeOfKnapsack(k, itemset) <= Capacity}
 
BestKnapsack(itemset) == 
  LET valid == ValidKnapsacks(itemset)
  IN CHOOSE k \in valid:
    \A k2 \in valid \ {k}:
      ValueOfKnapsack(k, itemset) >= ValueOfKnapsack(k2, itemset) 
      
BestKnapsacks(itemset) == 
  LET 
    valid == ValidKnapsacks(itemset) 
  IN 
    {k \in valid:
      ~ \E k2 \in valid \ {k}:
        ValueOfKnapsack(k, itemset) < ValueOfKnapsack(k2, itemset) 
    }
    
(*--algorithm debug 
variables 
  is \in ItemSet; 
begin 
  skip; 
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES is, pc

vars == << is, pc >>

Init == (* Global variables *)
        /\ is \in ItemSet
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ is' = is

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 17:51:48 EDT 2018 by benjamin
\* Created Tue Aug 14 16:27:17 EDT 2018 by benjamin
