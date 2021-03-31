---- MODULE MC ----
EXTENDS UnoScript, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_1617155911955125000 == 
8
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1617155911956126000 ==
USTypeOK /\ Len(stack) =< (N)
----
=============================================================================
\* Modification History
\* Created Tue Mar 30 20:58:31 CDT 2021 by quin
