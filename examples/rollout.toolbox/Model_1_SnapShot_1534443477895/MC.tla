---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534443470856724000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534443470856725000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534443470856726000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534443470856727000 ==
Availability
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534443470856728000 ==
VersionConsistency
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1534443470856729000 ==
UpdateSuccessful
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:17:50 EDT 2018 by benjamin
