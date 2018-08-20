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

=============================================================================
\* Modification History
\* Last modified Tue Aug 14 17:40:45 EDT 2018 by benjamin
\* Created Tue Aug 14 16:27:17 EDT 2018 by benjamin
