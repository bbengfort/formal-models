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
const_1534355626399423000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1534355626399424000 == 
{r1}
----

\* SYMMETRY definition
symm_1534355626399425000 == 
Permutations(const_1534355626399423000) \union Permutations(const_1534355626399424000)
----

\* CONSTANT definitions @modelParameterConstants:0MaxBuffer
const_1534355626399426000 == 
1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534355626399427000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534355626399428000 ==
AllThreadsStatus
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534355626399429000 ==
OccupiedCorrect
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 13:53:46 EDT 2018 by benjamin
