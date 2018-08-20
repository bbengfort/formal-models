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
const_1534356177083437000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1534356177083438000 == 
{r1}
----

\* SYMMETRY definition
symm_1534356177083439000 == 
Permutations(const_1534356177083437000) \union Permutations(const_1534356177083438000)
----

\* CONSTANT definitions @modelParameterConstants:0MaxBuffer
const_1534356177083440000 == 
1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534356177083441000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534356177083442000 ==
AllThreadsStatus
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534356177083443000 ==
OccupiedCorrect
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 14:02:57 EDT 2018 by benjamin
