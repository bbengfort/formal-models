---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534442493645691000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534442493645692000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534442493645693000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534442493645694000 ==
Availability
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534442493645695000 ==
VersionConsistency
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:01:33 EDT 2018 by benjamin
