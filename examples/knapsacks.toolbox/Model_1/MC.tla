---- MODULE MC ----
EXTENDS knapsacks, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Items
const_1534283590030188000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_1534283590030189000 == 
Permutations(const_1534283590030188000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1534283590030190000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Tue Aug 14 17:53:10 EDT 2018 by benjamin
