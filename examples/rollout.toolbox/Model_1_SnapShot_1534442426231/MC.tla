---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534442424210672000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534442424210673000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534442424210674000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534442424210675000 ==
Availability
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:00:24 EDT 2018 by benjamin
