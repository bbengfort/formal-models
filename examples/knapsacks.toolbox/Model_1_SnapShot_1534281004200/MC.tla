---- MODULE MC ----
EXTENDS knapsacks, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1534281003109140000 == 
<<BestKnapsack, ValueOfKnapsack(BestKnapsack)>>
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534281003109140000>>)
----

=============================================================================
\* Modification History
\* Created Tue Aug 14 17:10:03 EDT 2018 by benjamin
