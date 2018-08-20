---- MODULE MC ----
EXTENDS knapsacks, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1534280895471137000 == 
BestKnapsack
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534280895471137000>>)
----

=============================================================================
\* Modification History
\* Created Tue Aug 14 17:08:15 EDT 2018 by benjamin
