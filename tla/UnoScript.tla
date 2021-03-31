----------------------------- MODULE UnoScript -----------------------------
EXTENDS Integers, Sequences

\* Define the types of cards allowed in the stack and on the tape
StackCard == { "color", "wild", "operator" }
TapeCard  == StackCard \union { "control" }

\* The maximum length of the stack
CONSTANT N

VARIABLES stack, \* a sequence of StackCards
          head   \* an element of TapeCard

USTypeOK == /\ stack \in Seq(StackCard)
            /\ head \in TapeCard

\* Assert that there are no adjacent operator cards in sequence s
NoAdjacentOperators(s) == \A i \in 1..(Len(s)-1) : s[i] /= "operator" \/ s[i] /= s[i+1]

\* Assert properties about the stack that should always be true
USStackInvariant == /\ NoAdjacentOperators(stack)

\* The stack is initially empty, and head can be any card type
USInit == /\ stack = << >>
          /\ head \in TapeCard

\* If the stack is non-empty, return the first item,
\* Otherwise return "wild"
Top(s) == IF Len(s) > 0
          THEN Head(s)
          ELSE "wild"

\* If the sequence s is empty, return the empty sequence,
\* Otherwise return the sequence with the first item removed
Pop(s) == IF s = << >>
          THEN s
          ELSE Tail(s)

\* Push item e onto stack s
\* if this will not grow the stack past N elements
Push(s, e) == IF Len(s) < (N-1)
              THEN << e >> \o s
              ELSE s

\* The draw2 operator takes a sequence as input
\* and returns a set of all possible sequences after a draw2 operation is performed.
draw2(s) ==
  LET s_y == Pop(s)
        y == Top(s_y)
      s_x == Pop(s_y)
        x == Top(s_x)
   s_base == Pop(s_x)
  IN { 
       << y >>       \o s_base, \* mathematical operators +,-,*,/
                                \* and logical operators <, >, <=, >=, ==, !=, ||, &&
       << x, y >>    \o s_base, \* swap
       << y, y, x >> \o s_base, \* dup
       << x, y, x >> \o s_base, \* over
       << x >>       \o s_base, \* drop, store, print
       s_base,                  \* if/endif
       s                        \* logical operator !
     }
     \union { << z, x >> \o s_base : z \in StackCard } \* load from memory

\* The draw4 operator takes a sequence as input
\* and returns a set of all possible sequences after a draw4 operation is performed.
draw4(s) ==
  LET s_a == Pop(s)
        a == Top(s_a)
      s_b == Pop(s_a)
        b == Top(s_b)
      s_c == Pop(s_b)
        c == Top(s_c)
      s_d == Pop(s_c)
        d == Top(s_d)
   s_base == Pop(s_d)
       d2 == << a, b >>
       d1 == << c, d >>
  IN {
       d1 \o d2         \o s_base, \* 2Swap
       d2 \o d2 \o d1   \o s_base, \* 2Dup
       d1 \o d2 \o d1   \o s_base, \* 2Over
       d1               \o s_base, \* 2Drop
       << c, a, b, d >> \o s_base, \* Rot
       << d >>          \o s_base  \* if/else/endif
     }

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
                   /\ stack' \in { stack } \union draw2(stack) \union draw4(stack)

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

ControlOnColor == /\ head = "control"
                  /\ Top(stack) = "color"
                  /\ head' \in TapeCard
                  /\ stack' = Tail(stack)

ControlOnWild == /\ head = "control"
                 /\ Top(stack) = "wild"
                 /\ head' \in TapeCard
                 /\ stack' = Pop(stack)

ControlOnOperator == /\ head = "control"
                     /\ Top(stack) = "operator"
                     /\ head' \in TapeCard
                     /\ UNCHANGED stack

USNext == \/ ColorOnColor    \/ ColorOnWild    \/ ColorOnOperator
          \/ WildOnColor     \/ WildOnWild     \/ WildOnOperator
          \/ OperatorOnColor \/ OperatorOnWild \/ OperatorOnOperator
          \/ ControlOnColor  \/ ControlOnWild  \/ ControlOnOperator

USSpec == USInit /\ [][USNext]_<<stack, head>>

THEOREM USSpec => [](USTypeOK /\ Len(stack) =< N)


=============================================================================
\* Modification History
\* Last modified Tue Mar 30 20:57:57 CDT 2021 by quin
\* Created Sat Mar 27 09:31:22 CDT 2021 by quin
