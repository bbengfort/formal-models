---- MODULE MC ----
EXTENDS semaphore, TLC

\* CONSTANT definitions @modelParameterConstants:0Threads
const_1534370710154559000 == 
1..3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534370710154560000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534370710154561000 ==
AtMostOneCriticalSection
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 18:05:10 EDT 2018 by benjamin
