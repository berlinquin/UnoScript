----------------------------- MODULE UnoScript -----------------------------
EXTENDS Integers, Sequences

\* StackCard == { "color", "wild", "operator" }
\* TapeCard  == StackCard \union { "control" }

\* Define the types of cards allowed in the stack and on the tape
StackCard == { "color", "wild", "operator" }
TapeCard  == StackCard

\* The maximum length of the stack
CONSTANT N

VARIABLES stack, \* a sequence of StackCards
          head   \* an element of TapeCard

USTypeOK == /\ stack \in Seq(StackCard)
            /\ head \in TapeCard

\* The stack is initially empty, and head can be any card type
USInit == /\ stack = << >>
          /\ head \in TapeCard

\* If the stack is non-empty, return the first item,
\* Otherwise return "wild"
Top(s) == IF Len(s) > 0
          THEN Head(s)
          ELSE "wild"

\* Push item e onto stack s
\* if this will not grow the stack past N elements
Push(s, e) == IF Len(s) < N
              THEN << e >> \o s
              ELSE s

ColorOnColor == /\ head = "color"
                /\ Top(stack) = "color"
                /\ head' \in TapeCard
                /\ stack' \in { stack, Push(stack, "color") }

ColorOnWild == /\ head = "color"
               /\ Top(stack) = "wild"
               /\ head' \in TapeCard
               /\ stack' = Push(stack, "color")

ColorOnOperator == /\ head = "color"
                   /\ Top(stack) = "operator"
                   /\ head' \in TapeCard
                   /\ UNCHANGED stack \* TODO: implement operators

WildOnColor == /\ head = "wild"
               /\ Top(stack) = "color"
               /\ head' \in TapeCard
               /\ stack' = Push(stack, "wild")

WildOnWild == /\ head = "wild"
              /\ Top(stack) = "wild"
              /\ head' \in TapeCard
              /\ UNCHANGED stack

WildOnOperator == /\ head = "wild"
                  /\ Top(stack) = "operator"
                  /\ head' \in TapeCard
                  /\ UNCHANGED stack

OperatorOnColor == /\ head = "operator"
                   /\ Top(stack) = "color"
                   /\ head' \in TapeCard
                   /\ stack' = Push(stack, "operator")

OperatorOnWild == /\ head = "operator"
                  /\ Top(stack) = "wild"
                  /\ head' \in TapeCard
                  /\ stack' = Push(stack, "operator")

OperatorOnOperator == /\ head = "operator"
                      /\ Top(stack) = "operator"
                      /\ head' \in TapeCard
                      /\ UNCHANGED stack

USNext == \/ ColorOnColor \/ ColorOnWild \/ ColorOnOperator
          \/ WildOnColor \/ WildOnWild \/ WildOnOperator
          \/ OperatorOnColor \/ OperatorOnWild \/ OperatorOnOperator

USSpec == USInit /\ [][USNext]_<<stack, head>>

THEOREM USSpec => [](USTypeOK /\ Len(stack) =< N)


=============================================================================
\* Modification History
\* Last modified Sat Mar 27 15:25:10 CDT 2021 by quin
\* Created Sat Mar 27 09:31:22 CDT 2021 by quin
