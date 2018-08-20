---- MODULE MC ----
EXTENDS bounded_buffer, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Writers
const_1534354448092374000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1534354448092375000 == 
{r1, r2}
----

\* CONSTANT definitions @modelParameterConstants:0MaxBuffer
const_1534354448092376000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534354448092377000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 13:34:08 EDT 2018 by benjamin
