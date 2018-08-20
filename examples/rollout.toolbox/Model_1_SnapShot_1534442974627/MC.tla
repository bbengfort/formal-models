---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534442965587701000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534442965587702000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534442965587703000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534442965587704000 ==
Availability
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534442965587705000 ==
VersionConsistency
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:09:25 EDT 2018 by benjamin
