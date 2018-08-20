---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534442454645681000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534442454645682000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534442454645683000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534442454645684000 ==
Availability
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534442454645685000 ==
Consistency
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:00:54 EDT 2018 by benjamin
