---- MODULE MC ----
EXTENDS bounded_buffer, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1
----

\* MV CONSTANT definitions Writers
const_1534354781280397000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1534354781280398000 == 
{r1}
----

\* SYMMETRY definition
symm_1534354781280399000 == 
Permutations(const_1534354781280397000) \union Permutations(const_1534354781280398000)
----

\* CONSTANT definitions @modelParameterConstants:0MaxBuffer
const_1534354781280400000 == 
1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534354781280401000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 13:39:41 EDT 2018 by benjamin
