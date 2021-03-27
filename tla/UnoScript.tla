----------------------------- MODULE UnoScript -----------------------------
EXTENDS Sequences

\* Define the types of cards allowed in the stack and on the tape
StackCard == { "color", "wild", "operator" }
TapeCard  == StackCard \union { "control" }

VARIABLES stack, \* a sequence of StackCards
          head   \* an element of TapeCard, giving the type of the current card under the head

USTypeOK == /\ stack \in Seq(StackCard)
            /\ head \in TapeCard

USInit == /\ stack = << >>
          /\ head \in TapeCard

ColorOnColor == /\ head = "color"
                /\ Head(stack) = "color"
                /\ head' \in TapeCard
                /\ stack' \in {stack, {"color"} \o stack}

USNext == ColorOnColor


=============================================================================
\* Modification History
\* Last modified Sat Mar 27 10:24:39 CDT 2021 by quin
\* Created Sat Mar 27 09:31:22 CDT 2021 by quin
