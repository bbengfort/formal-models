---- MODULE MC ----
EXTENDS bounded_buffer, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2, w3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions Writers
const_1534354675671387000 == 
{w1, w2, w3}
----

\* MV CONSTANT definitions Readers
const_1534354675671388000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_1534354675671389000 == 
Permutations(const_1534354675671387000) \union Permutations(const_1534354675671388000)
----

\* CONSTANT definitions @modelParameterConstants:0MaxBuffer
const_1534354675671390000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534354675671391000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 13:37:55 EDT 2018 by benjamin
