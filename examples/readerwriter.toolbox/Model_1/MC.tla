---- MODULE MC ----
EXTENDS readerwriter, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxQueueSize
const_1534349844916294000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1534349844916295000 ==
dropped_count < 4
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534349844916296000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534349844916297000 ==
BoundedQueue
----
=============================================================================
\* Modification History
\* Created Wed Aug 15 12:17:24 EDT 2018 by benjamin
