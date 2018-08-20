---- MODULE MC ----
EXTENDS semaphore, TLC

\* CONSTANT definitions @modelParameterConstants:0Threads
const_1534370785168573000 == 
1..3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534370785168574000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534370785168575000 ==
AtMostOneCriticalSection
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534370785168576000 ==
TypeInvariant
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 18:06:25 EDT 2018 by benjamin
