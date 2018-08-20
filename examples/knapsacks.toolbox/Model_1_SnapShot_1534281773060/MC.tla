---- MODULE MC ----
EXTENDS knapsacks, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1534281768033148000 == 
{BestKnapsack(is): is \in ItemSet}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534281768033148000>>)
----

=============================================================================
\* Modification History
\* Created Tue Aug 14 17:22:48 EDT 2018 by benjamin
