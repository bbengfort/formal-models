---- MODULE MC ----
EXTENDS knapsacks, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1534282403580152000 == 
{BestKnapsacks(is): is \in ItemSet}

----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534282403580152000>>)
----

=============================================================================
\* Modification History
\* Created Tue Aug 14 17:33:23 EDT 2018 by benjamin
