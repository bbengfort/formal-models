---- MODULE MC ----
EXTENDS wire, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
alice, bob, eve
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2, t3
----

\* MV CONSTANT definitions People
const_1534284936064231000 == 
{alice, bob, eve}
----

\* MV CONSTANT definitions Wires
const_1534284936064232000 == 
{t1, t2, t3}
----

\* CONSTANT definitions @modelParameterConstants:1MoneyRange
const_1534284936064233000 == 
0..3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534284936064234000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534284936064235000 ==
NoOverdrafts
----
=============================================================================
\* Modification History
\* Created Tue Aug 14 18:15:36 EDT 2018 by benjamin
