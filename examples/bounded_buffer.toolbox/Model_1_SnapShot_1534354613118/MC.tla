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
const_1534354605072378000 == 
{w1, w2}
----

\* MV CONSTANT definitions Readers
const_1534354605072379000 == 
{r1, r2}
----

\* CONSTANT definitions @modelParameterConstants:0MaxBuffer
const_1534354605072380000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534354605072381000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 13:36:45 EDT 2018 by benjamin
