---- MODULE MC ----
EXTENDS UnoScript, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_161695386062388000 == 
8
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_161695386062389000 ==
USTypeOK /\ Len(stack) =< (N)
----
=============================================================================
\* Modification History
\* Created Sun Mar 28 12:51:00 CDT 2021 by quin
