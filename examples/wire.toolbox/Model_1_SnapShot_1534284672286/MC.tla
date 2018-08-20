---- MODULE MC ----
EXTENDS wire, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
alice, bob, eve
----

\* MV CONSTANT definitions People
const_1534284655230212000 == 
{alice, bob, eve}
----

\* CONSTANT definitions @modelParameterConstants:1MoneyRange
const_1534284655230213000 == 
0..10
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534284655230214000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534284655230215000 ==
NoOverdrafts
----
=============================================================================
\* Modification History
\* Created Tue Aug 14 18:10:55 EDT 2018 by benjamin
