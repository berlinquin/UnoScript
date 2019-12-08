# Uno Language Specifications

Uno is a stack-based programming language inspired by the UNO card game.
It works from these design principles:

- The alphabet consists of the set of cards in the UNO card game
- Any sequence of the symbols from this alphabet must be an acceptable and executable program
- The language will be Turing complete if restrictions on the set of cards are relaxed

# The Alphabet

Following the design goals, the alphabet consists of the set of cards in the UNO card game.

A standard UNO deck contains:

- Blue, green, red, and yellow cards with values from 0 to 9
- Draw Two cards in blue, green, red and yellow
- Reverse cards in blue, green, red and yellow
- Skip cards in blue, green, red and yellow
- Wild cards
- Wild Draw Four cards 

Translating these cards into symbols for the language, only standard number cards have retained their color.
So, draw two, reverse, and skip cards of different colors are treated as identical.

These cards are represented in an Uno program using the following symbols, expressed as regular expressions:

- `[bgry][0-9]` Represents a standard color card.
The first character represents the color of the card, the second its value.
Also referred to as `color` throughout the document. 

- `draw2` Represents a draw two card
- `reverse` Represents a reverse card
- `skip` Represets a skip card
- `wild` Represents a wild card
- `draw4` Represents a draw four card

# Model of Execution

Before it begins to interpret an Uno program, the Uno interpreter initializes an empty stack capable of holding integers and symbols in the language.
It also initializes 4 independent arrays of integers, all of length ten.
It also sets the seek direction, used by control flow constructs, to point to the right.
Once these are initialized, the interpreter begins to read the program in.

An Uno program consists of a linear sequence of the previously defined symbols.
The interpreter has a head, initially positioned at the first symbol, that identifies the next symbol to be recognized.
For each symbol that it recognizes, the interpreter can choose to read values from the stack, push values onto the stack,
access one of the four arrays, and/or move the instruction pointer to the next instruction which should be executed.

# Semantics

When processing a new symbol, the meaning assigned to it by the interpreter depends on the top value of the stack.
This allows a symbol to be treated either as data to be pushed to the stack or as an operation on the stack.
Additionally, some control flow constructs will use symbols as markers in the program.

To specify the language, the symbols will be classified into four categories.

The categories are:

- Color cards = { color }
- Wild cards = { wild }
- Operator cards = { draw2, draw4 }
- Control flow cards = { skip, reverse }

The input alphabet is the set { color, wild, operator, control\_flow }, and the stack alphabet the set { color, wild, operator }.
The operation of the interpreter be explained in terms of the 12 possible configurations,
which are given by the symbol under the head and the symbol at the top of the stack.

Head | Stack | Operation
-----|-------|----------
Color | Color    | If the colors match, then the value on the stack is multiplied by 10, the value under the head is added to it, and the modified value is pushed to the stack. If the colors do not match, then the symbol under the head is pushed to the stack.
Color | Wild     | The color card replaces the wild on the stack.
Color | Operator | The operator takes the color card and uses it to look up which operation should be performed. If no operation is associated with the given color card, this is a no-op and the stack is unmodified.
Wild | Color    | The wild is pushed to the stack.
Wild | Wild     | No-op
Wild | Operator | No-op
Operator | Color    | The operator is pushed to the stack.
Operator | Wild     | The operator is pushed to the stack.
Operator | Operator | The operator on the stack is replaced by the operator under the head.
Control flow | Color    | The color is popped from the stack, and used as the label to search for by the control flow statement.
Control flow | Wild     | The wild is popped from the stack, and used as the label to search for by the control flow statement.
Control flow | Operator | No-op

# Operators

An operator card is either a draw2 or a draw4 card, where draw2 cards operate on the top two values of the stack and draw4 on the top four.
The Forth stack documentation convention is used to show how the stack is manipulated by the operation.
Also note that the stack manipulation operators are borrowed directly from Forth,
see the [Forth manual](https://www.forth.com/starting-forth/2-stack-manipulation-operators-arithmetic/#Chapter_Summary) for details.

Here are the available draw2 operators.
For the initial four mathematical operations, the color of the result takes the color of the top card (`y` in the stack diagram).

Color card | Stack | Operation
-----------|-------|----------
r0 | `( x y -- x+y )` |  Add
y0 | `( x y -- x-y )` | Subtract
g0 | `( x y -- x*y )` | Multiply
b0 | `( x y -- x/y )` | Divide
r1 | `( x y -- y x )` | Swap
y1 | `( x -- x x )` | Dup
g1 | `( x y -- x y x )` | Over
b1 | `( x -- )` | Drop
r2 | `( x y -- x )` | Put value `x` in its color array at index `y % 10` 
y2 | `( y -- array[y] )` | Get the value of the color array at index `y % 10` and push it to the stack
g2 | `( x -- x )` | Print the ascii character with the value of `x`
b2 | `( x y -- )` | if/endif. If `x` is true, then execute code until symbol `y` is encountered. Otherwise skip directly to symbol `y`.

Here are the available draw4 operators.

Color card | Stack | Operation
-----------|-------|----------
r0 | 
y0 | 
g0 | 
b0 | 
r1 | `( d1 d2 -- d2 d1 )` | 2Swap
y1 | `( d1 -- d1 d1 )` | 2Dup
g1 | `( d1 d2 -- d1 d2 d1 )` | 2Over
b1 | `( d1 -- )` | 2Drop
r2 | `( x y z -- y z x)` | Rot
y2 | 
g2 | 
b2 | `( x y z -- )` | if/else/endif. If `x` is true, execute all code until symbol `y` then jump to `z`. If `x` is false, jump to `y` and execute all code until symbol `z`.

# Control Flow

The head's location, which determines which symbol is read next, can be manipulated directly with the control flow constructs (skip and reverse)
or with the if/endif and if/else/endif operators.

## Skip & Reverse

Both the skip and reverse constructs take two parameters: the top value of the stack and the seek direction.
The top value of the stack is popped, and the head moves in the seek direction (which is set to the right at runtime) until it encounters that exact value again.
When a match is found, the head moves to the right, without pushing the match to the stack, and resumes execution.

Reverse differs from skip in that it flips the value of the seek direction after the match has been found.

Construct | Stack | Behavior | Seek direction changed
----------|-------|----------|-----------------------
skip      | `( x -- )` | Skip moves the head in the seek direction until a matching `x` is found, or the beginning/end of the program is reached | No
reverse   | `( x -- )` | Reverse moves the head in the seek direction until a matching `x` is found, or the beginning/end of the program is reached | Yes

If no match if found, then the head is either at the end of the program or the beginning.
If at the beginning, the seek direction is reset to point to the right and execution resumes.
If at the end, then the program exits without error.

## Conditional operators

In the case of conditionals, moving the head like this is handled by the interpreter and always moves to the right, independent of the seek direction.
They also follow the same convention as skip and reverse by ensuring that the matching symbol is not pushed to the stack.

If no match is found, and the head reaches the end of the program, then the program exits without error.

