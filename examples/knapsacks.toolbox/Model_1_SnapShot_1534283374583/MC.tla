---- MODULE MC ----
EXTENDS knapsacks, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Items
const_1534283362529157000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_1534283362529158000 == 
Permutations(const_1534283362529157000)
----

\* Constant expression definition @modelExpressionEval
const_expr_1534283362529159000 == 
{BestKnapsacks(is): is \in ItemSet}

----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534283362529159000>>)
----

=============================================================================
\* Modification History
\* Created Tue Aug 14 17:49:22 EDT 2018 by benjamin
