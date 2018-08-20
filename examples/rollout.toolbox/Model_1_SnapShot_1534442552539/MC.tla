---- MODULE MC ----
EXTENDS rollout, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Servers
const_1534442550511696000 == 
{s1, s2, s3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534442550511697000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534442550511698000 ==
TypeInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534442550511699000 ==
Availability
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1534442550511700000 ==
VersionConsistency
----
=============================================================================
\* Modification History
\* Created Thu Aug 16 14:02:30 EDT 2018 by benjamin
