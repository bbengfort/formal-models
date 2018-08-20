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
const_1534354394859370000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1534354394859371000 == 
{r1, r2}
----

\* CONSTANT definitions @modelParameterConstants:0MaxBuffer
const_1534354394859372000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534354394859373000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 13:33:14 EDT 2018 by benjamin
