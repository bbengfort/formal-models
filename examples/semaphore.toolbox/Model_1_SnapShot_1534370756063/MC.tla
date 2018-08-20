---- MODULE MC ----
EXTENDS semaphore, TLC

\* CONSTANT definitions @modelParameterConstants:0Threads
const_1534370748018562000 == 
1..3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534370748018563000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534370748018564000 ==
AtMostOneCriticalSection
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 18:05:48 EDT 2018 by benjamin
