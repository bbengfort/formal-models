---- MODULE MC ----
EXTENDS wire, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
alice, bob, eve
----

\* MV CONSTANT definitions People
const_1534284844369221000 == 
{alice, bob, eve}
----

\* CONSTANT definitions @modelParameterConstants:1MoneyRange
const_1534284844369222000 == 
0..3
----

\* CONSTANT definitions @modelParameterConstants:2Wires
const_1534284844369223000 == 
1..3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534284844369224000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534284844369225000 ==
NoOverdrafts
----
=============================================================================
\* Modification History
\* Created Tue Aug 14 18:14:04 EDT 2018 by benjamin
