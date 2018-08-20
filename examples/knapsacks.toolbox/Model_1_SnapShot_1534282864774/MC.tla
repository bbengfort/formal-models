---- MODULE MC ----
EXTENDS knapsacks, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1534282852722153000 == 
{BestKnapsacks(is): is \in ItemSet}

----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534282852722153000>>)
----

=============================================================================
\* Modification History
\* Created Tue Aug 14 17:40:52 EDT 2018 by benjamin
