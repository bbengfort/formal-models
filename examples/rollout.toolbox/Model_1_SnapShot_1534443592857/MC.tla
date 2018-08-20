---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534443585824730000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534443585824731000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534443585824732000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534443585824733000 ==
Availability
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534443585824734000 ==
VersionConsistency
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1534443585824735000 ==
UpdateSuccessful
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:19:45 EDT 2018 by benjamin
