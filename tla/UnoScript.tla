----------------------------- MODULE UnoScript -----------------------------
EXTENDS Integers, Sequences

\* Define the types of cards allowed in the stack and on the tape
StackCard == { "color", "wild", "operator" }
TapeCard  == StackCard \union { "control" }

\* The maximum length of the tape
CONSTANT TAPE_N
\* The maximum length of the stack to be considered
CONSTANT STACK_N

VARIABLES tape,  \* a sequence of TapeCards
          head,  \* an index into tape giving the location of the head
          stack  \* a sequence of StackCards

vars == << tape, head, stack >>

\* Return a set of all functions with domains from 0 to n
\* that map to items in the given set.
\* (i.e. tuples with length <= n)
\* Borrowed from: https://www.hillelwayne.com/post/tla-messages/
SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}

\* Type invariant for the tape state variables
TapeTypeOK == /\ SubSeq(tape, 2, Len(tape)-1) \in SeqOf(TapeCard, TAPE_N) \* the set of sequences of TapeCards with length < N
              /\ head \in 1..Len(tape)

\* Type invariant for the stack state variables
StackTypeOK == /\ stack \in Seq(StackCard)

\* Assert that there are no adjacent operator cards in sequence s
NoAdjacentOperators(s) == \A i \in 1..(Len(s)-1) : s[i] /= "operator" \/ s[i] /= s[i+1]

\* Assert properties about the stack that should always be true
USStackInvariant == /\ Len(stack) =< STACK_N
                    /\ NoAdjacentOperators(stack)

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

\* The tape is set to a program with length <= N,
\* head starts over the first card in tape,
\* and top is a wild card
USInit == /\ tape \in { <<"start">> \o t \o <<"stop">> : t \in SeqOf(TapeCard, TAPE_N) }
          /\ head = 1
          /\ stack = << >>

\* Initial transition allowed when head is on starting position
HeadOnStart == /\ tape[head] = "start"
               /\ head' = head + 1
               /\ UNCHANGED << tape, stack >>

\* Head has reached the end of the tape. Only this action is enabled.
HeadOnStop == /\ tape[head] = "stop"
              /\ UNCHANGED vars

\* Modify the current color card on the stack,
\* or push a new color card
ColorOnColor == /\ tape[head] = "color"
                /\ Top(stack) = "color"
                /\ head' = head + 1
                /\ stack' \in Prune_set({ stack, Push(stack, "color") })
                /\ UNCHANGED tape

\* Push a color card to the stack
ColorOnWild == /\ tape[head] = "color"
               /\ Top(stack) = "wild"
               /\ head' = head + 1
               /\ stack' = Prune(Push(stack, "color"))
               /\ UNCHANGED tape

\* Do the operation associated with operator, if any
ColorOnOperator == /\ tape[head] = "color"
                   /\ Top(stack) = "operator"
                   /\ head' = head + 1
                   /\ stack' \in Prune_set({ stack } \union draw2(stack) \union draw4(stack))
                   /\ UNCHANGED tape

\* Push the wild card to the stack
WildOnColor == /\ tape[head] = "wild"
               /\ Top(stack) = "color"
               /\ head' = head + 1
               /\ stack' = Prune(Push(stack, "wild"))
               /\ UNCHANGED tape

\* Do nothing, increment the head to the next card
WildOnWild == /\ tape[head] = "wild"
              /\ Top(stack) = "wild"
              /\ head' = head + 1
              /\ UNCHANGED << tape, stack >>

\* Do nothing, increment the head to the next card
WildOnOperator == /\ tape[head] = "wild"
                  /\ Top(stack) = "operator"
                  /\ head' = head + 1
                  /\ UNCHANGED << tape, stack >>

\* Push the operator to the stack
OperatorOnColor == /\ tape[head] = "operator"
                   /\ Top(stack) = "color"
                   /\ head' = head + 1
                   /\ stack' = Prune(Push(stack, "operator"))
                   /\ UNCHANGED tape

\* Push the operator to the stack
OperatorOnWild == /\ tape[head] = "operator"
                  /\ Top(stack) = "wild"
                  /\ head' = head + 1
                  /\ stack' = Prune(Push(stack, "operator"))
                  /\ UNCHANGED tape

\* Replace the operator on the stack
OperatorOnOperator == /\ tape[head] = "operator"
                      /\ Top(stack) = "operator"
                      /\ head' = head + 1
                      /\ UNCHANGED << tape, stack >>

\* Pop the color card from the stack.
\* Set the location of the head to the start or stop of the tape,
\* Or to some color card on the tape.
ControlOnColor == /\ tape[head] = "control"
                  /\ Top(stack) = "color"
                  /\ head' \in { i \in 1..Len(tape) : tape[i] \in { "color", "start", "stop" } /\ i /= head-1 }
                  /\ stack' = Pop(stack)
                  /\ UNCHANGED tape

\* Pop the wild from the stack.
\* Set the location of the head to the start or stop of the tape,
\* Or to some wild card on the tape.
ControlOnWild == /\ tape[head] = "control"
                 /\ Top(stack) = "wild"
                 /\ head' \in { i \in 1..Len(tape) : tape[i] \in { "wild", "start", "stop" } /\ i /= head-1 }
                 /\ stack' = Pop(stack)
                 /\ UNCHANGED tape

\* Do nothing, increment the head to the next card
ControlOnOperator == /\ tape[head] = "control"
                     /\ Top(stack) = "operator"
                     /\ head' = head + 1
                     /\ UNCHANGED << tape, stack >>

USNormalOperation ==
   \/ HeadOnStart     \/ HeadOnStop
   \/ ColorOnColor    \/ ColorOnWild    \/ ColorOnOperator
   \/ WildOnColor     \/ WildOnWild     \/ WildOnOperator
   \/ OperatorOnColor \/ OperatorOnWild \/ OperatorOnOperator
   \/ ControlOnColor  \/ ControlOnWild  \/ ControlOnOperator

USSpec == USInit /\ [][USNormalOperation]_vars

THEOREM USSpec => [](TapeTypeOK /\ StackTypeOK /\ USStackInvariant)


=============================================================================
\* Modification History
\* Last modified Sat Jun 26 15:20:22 CDT 2021 by quin
\* Created Sat Jun 26 15:19:07 CDT 2021 by quin
