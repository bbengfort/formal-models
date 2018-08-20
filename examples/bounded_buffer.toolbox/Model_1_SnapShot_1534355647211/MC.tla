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
const_1534355645189430000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1534355645189431000 == 
{r1}
----

\* SYMMETRY definition
symm_1534355645189432000 == 
Permutations(const_1534355645189430000) \union Permutations(const_1534355645189431000)
----

\* CONSTANT definitions @modelParameterConstants:0MaxBuffer
const_1534355645189433000 == 
1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534355645189434000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534355645189435000 ==
AllThreadsStatus
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534355645189436000 ==
OccupiedCorrect
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 13:54:05 EDT 2018 by benjamin
