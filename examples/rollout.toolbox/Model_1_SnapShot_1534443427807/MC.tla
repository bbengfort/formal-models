---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534443418770718000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534443418770719000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534443418770720000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534443418770721000 ==
Availability
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534443418770722000 ==
VersionConsistency
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1534443418770723000 ==
UpdateSuccessful
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:16:58 EDT 2018 by benjamin
