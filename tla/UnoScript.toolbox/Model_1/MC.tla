---- MODULE MC ----
EXTENDS UnoScript, TLC

\* CONSTANT definitions @modelParameterConstants:0STACK_N
const_1617754772328331000 == 
8
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1617754772329332000 ==
USTypeOK /\ Len(stack) =< (STACK_N)
----
=============================================================================
\* Modification History
\* Created Tue Apr 06 19:19:32 CDT 2021 by quin
