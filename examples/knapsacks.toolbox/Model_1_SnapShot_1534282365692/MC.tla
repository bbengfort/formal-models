---- MODULE MC ----
EXTENDS knapsacks, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1534282364580151000 == 
BestKnapsacks(HardcodedItemSet)

----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1534282364580151000>>)
----

=============================================================================
\* Modification History
\* Created Tue Aug 14 17:32:44 EDT 2018 by benjamin
