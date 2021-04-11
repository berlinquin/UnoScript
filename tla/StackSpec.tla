----------------------------- MODULE StackSpec -----------------------------
EXTENDS Integers, Sequences

\* Define the types of cards allowed in the stack and on the tape
StackCard == { "color", "wild", "operator" }
TapeCard  == StackCard \union { "control" }

\* The maximum length of the stack to be considered
CONSTANT STACK_N

VARIABLES stack, \* a sequence of StackCards
          head   \* an element of TapeCard

\* Type invariant for the state variables
USTypeOK == /\ stack \in Seq(StackCard)
            /\ head \in TapeCard

\* Assert that there are no adjacent operator cards in sequence s
NoAdjacentOperators(s) == \A i \in 1..(Len(s)-1) : s[i] /= "operator" \/ s[i] /= s[i+1]

\* Assert properties about the stack that should always be true
USStackInvariant == /\ Len(stack) =< STACK_N
                    /\ NoAdjacentOperators(stack)

\* The stack is initially empty, and head can be any card type
USInit == /\ stack = << >>
          /\ head \in TapeCard

\* If the stack is non-empty, return the first item,
\* Otherwise return "wild"
Top(s) == IF s /= << >>
          THEN Head(s)
          ELSE "wild"

\* If the sequence s is empty, return the empty sequence,
\* Otherwise return the sequence with the first item removed
Pop(s) == IF s = << >>
          THEN s
          ELSE Tail(s)

\* Push item e onto stack s
Push(s, e) == << e >> \o s

\* Take a sequence as input,
\* returning the same sequence if it's below the upper bound on length,
\* or the sequence reduced to STACK_N elements otherwise.
RECURSIVE Prune(_)
Prune(s) ==
  IF Len(s) =< STACK_N
  THEN s
  ELSE Prune(Pop(s))

\* Take a set of sequences as input
\* and return all sequences with length leq the constant STACK_N.
Prune_set(stacks) == { s \in stacks : Len(s) =< STACK_N }

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
                                \* and logical operators <, >, <=, >=, =, !=, ||, &&
       << x, y >>    \o s_base, \* swap
       << y, y, x >> \o s_base, \* dup
       << x, y, x >> \o s_base, \* over
       << x >>       \o s_base, \* drop, store, print
                        s_base, \* if/endif
                             s  \* logical operator !
     }
     \union { << z, x >> \o s_base : z \in StackCard } \* load card from memory

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
       << c, a, b, d >> \o s_base, \* Rotate
       << d >>          \o s_base  \* if/else/endif
     }

ColorOnColor == /\ head = "color"
                /\ Top(stack) = "color"
                /\ head' \in TapeCard
                /\ stack' \in Prune_set({ stack, Push(stack, "color") })

ColorOnWild == /\ head = "color"
               /\ Top(stack) = "wild"
               /\ head' \in TapeCard
               /\ stack' = Prune(Push(stack, "color"))

ColorOnOperator == /\ head = "color"
                   /\ Top(stack) = "operator"
                   /\ head' \in TapeCard
                   /\ stack' \in Prune_set({ stack } \union draw2(stack) \union draw4(stack))

WildOnColor == /\ head = "wild"
               /\ Top(stack) = "color"
               /\ head' \in TapeCard
               /\ stack' = Prune(Push(stack, "wild"))

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
                   /\ stack' = Prune(Push(stack, "operator"))

OperatorOnWild == /\ head = "operator"
                  /\ Top(stack) = "wild"
                  /\ head' \in TapeCard
                  /\ stack' = Prune(Push(stack, "operator"))

OperatorOnOperator == /\ head = "operator"
                      /\ Top(stack) = "operator"
                      /\ head' \in TapeCard
                      /\ UNCHANGED stack

ControlOnColor == /\ head = "control"
                  /\ Top(stack) = "color"
                  /\ head' \in TapeCard
                  /\ stack' = Pop(stack)

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

THEOREM USSpec => [](USTypeOK /\ USStackInvariant)


=============================================================================
\* Modification History
\* Last modified Sat Apr 10 20:45:13 CDT 2021 by quin
\* Created Sat Mar 27 09:31:22 CDT 2021 by quin
