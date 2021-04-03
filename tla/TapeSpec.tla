------------------------------ MODULE TapeSpec ------------------------------
EXTENDS Integers, Sequences

\* Define the types of cards allowed in the stack and on the tape
StackCard == { "color", "wild", "operator" }
TapeCard  == StackCard \union { "control" }
\* The direction the tape head is moving
ScanDirection == { "normal", "left", "right" }

\* The maximum length of the tape
CONSTANT TAPE_N

VARIABLES tape, \* a sequence of TapeCards
          head, \* an index into tape giving the location of the head
          top,  \* an element of StackCard
          scan

vars == << tape, head, top, scan >>

\* Borrowed from H. Wayne's site.
\* Return a set of all functions with domains from 0 to n
\* (i.e. tuples with length <= n)
\* that map to items in the given set
SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}

\* Type invariant for the state variables
USTypeOK == /\ SubSeq(tape, 2, Len(tape)-1) \in SeqOf(TapeCard, TAPE_N) \* the set of sequences of TapeCards with length < N
            /\ head \in 1..Len(tape)
            /\ top \in StackCard
            /\ scan \in ScanDirection

\* The tape is set to a program with length <= N,
\* head starts over the first card in tape,
\* and top is a wild card
USInit == /\ tape \in { <<"start">> \o t \o <<"stop">> : t \in SeqOf(TapeCard, TAPE_N) }
          /\ head = 1
          /\ top = "wild"
          /\ scan = "normal"

\* Initial transition allowed when head is on starting position
HeadOnStart == /\ tape[head] = "start"
               /\ head' = head + 1
               /\ UNCHANGED << tape, scan, top >>

\* Head has reached the end of the tape. Only this action is enabled.
HeadOnStop == /\ tape[head] = "stop"
              /\ UNCHANGED vars

\* Modify the current color card on the stack,
\* or push a new color card
ColorOnColor == /\ tape[head] = "color"
                /\ top = "color"
                /\ head' = head + 1
                /\ UNCHANGED << tape, scan, top >>

\* Push a color card to the stack
ColorOnWild == /\ tape[head] = "color"
               /\ top = "wild"
               /\ head' = head + 1
               /\ top' = "color"
               /\ UNCHANGED << tape, scan >>

\* Do the operation associated with operator, if any
ColorOnOperator == /\ tape[head] = "color"
                   /\ top = "operator"
                   /\ head' = head + 1
                   /\ top' \in StackCard \* top is the result of the operation
                   /\ UNCHANGED << tape, scan >>

\* Push the wild card to the stack
WildOnColor == /\ tape[head] = "wild"
               /\ top = "color"
               /\ head' = head + 1
               /\ top' = "wild"
               /\ UNCHANGED << tape, scan >>

\* Do nothing, increment the head to the next card
WildOnWild == /\ tape[head] = "wild"
              /\ top = "wild"
              /\ head' = head + 1
              /\ UNCHANGED << tape, scan, top >>

\* Do nothing, increment the head to the next card
WildOnOperator == /\ tape[head] = "wild"
                  /\ top = "operator"
                  /\ head' = head + 1
                  /\ UNCHANGED << tape, scan, top >>

\* Push the operator to the stack
OperatorOnColor == /\ tape[head] = "operator"
                   /\ top = "color"
                   /\ head' = head + 1
                   /\ top' = "operator"
                   /\ UNCHANGED << tape, scan >>

\* Push the operator to the stack
OperatorOnWild == /\ tape[head] = "operator"
                  /\ top = "wild"
                  /\ head' = head + 1
                  /\ top' = "operator"
                  /\ UNCHANGED << tape, scan >>

\* Replace the operator on the stack
OperatorOnOperator == /\ tape[head] = "operator"
                      /\ top = "operator"
                      /\ head' = head + 1
                      /\ UNCHANGED << tape, scan, top >>

\* Pop the color card from the stack,
\* Optionally set the direction of movement
ControlOnColor == /\ tape[head] = "control"
                  /\ top = "color"
                  /\ head' = head + 1
                  /\ top' \in StackCard \* Whatever was below the color card
                  /\ scan' \in {"left", "right"}
                  /\ UNCHANGED tape

\* Pop the wild from the stack,
\* Optionally set the direction of movement
ControlOnWild == /\ tape[head] = "control"
                 /\ top = "wild"
                 /\ head' = head + 1
                 /\ top' \in StackCard \* Whatever was below the wild card
                 /\ scan' \in {"left", "right"}
                 /\ UNCHANGED tape

\* Do nothing, increment the head to the next card
ControlOnOperator == /\ tape[head] = "control"
                     /\ top = "operator"
                     /\ head' = head + 1
                     /\ UNCHANGED << tape, scan, top >>

USNormalOperation ==
   /\ scan = "normal"
   /\ \/ HeadOnStart     \/ HeadOnStop
      \/ ColorOnColor    \/ ColorOnWild    \/ ColorOnOperator
      \/ WildOnColor     \/ WildOnWild     \/ WildOnOperator
      \/ OperatorOnColor \/ OperatorOnWild \/ OperatorOnOperator
      \/ ControlOnColor  \/ ControlOnWild  \/ ControlOnOperator

USSpec == USInit /\ [][USNormalOperation]_vars

THEOREM USSpec => []USTypeOK


=============================================================================
\* Modification History
\* Last modified Sat Apr 03 15:07:41 CDT 2021 by quin
\* Created Fri Apr 02 10:32:07 CDT 2021 by quin
