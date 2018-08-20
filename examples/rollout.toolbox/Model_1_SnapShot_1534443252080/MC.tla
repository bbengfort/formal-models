---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534443244043712000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534443244043713000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534443244043714000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534443244043715000 ==
Availability
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534443244043716000 ==
VersionConsistency
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1534443244043717000 ==
UpdateSuccessful
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:14:04 EDT 2018 by benjamin
