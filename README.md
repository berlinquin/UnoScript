# UnoScript

UnoScript is a general-purpose, stack-based programming language inspired by the UNO card game.
It aims to maximize usability while meeting the constraint that every sequence of UNO cards is a valid program in the language.

This repository holds:
- The [language specification](specs.md)
- An interpreter which implements the specification
- A few [example programs](./examples)
- A [formal specification](./tla) written in TLA+

## Building the Interpreter

The interpreter is written in C++, with dependencies on [flex](https://github.com/westes/flex), [gcc](https://gcc.gnu.org/), and [make](https://www.gnu.org/software/make/).

To build the interpreter, open a terminal, `cd` into the project directory and run `make`.
The Makefile expects that the executables `flex` and `g++` are available on your terminal's PATH.

This will compile the interpreter source and create an executable named `uno`.

## Running Programs

UnoScript programs can be run by passing them as input to the `uno` executable.
By convention, UnoScript programs use the file extension ".uno".

For example, to run the hello world program, run this from the project root:

`./uno < examples/hello_world.uno`

## Verbose Mode

To aid in writing UnoScript programs the interpreter provides a verbose mode.

In verbose mode, as each instruction is processed, the interpreter prints out:
- The program source, with an arrow indicating the position of the head
- The top five items on the stack

To enable this, pass the `-v` or `--verbose` flag to the interpreter, for example:

`./uno --verbose < examples/hello_world.uno`

### Interpreting verbose output

For example, the output below shows an addition operation.

In the first state, a `draw2` card is at the top of the stack with the head over a `r0` card.
The head reads the `r0` card, pops the `draw2` off the stack, and operates on the top two items on the stack.

`r0` corresponds to addition, so the top of the stack is replaced with `g0 + b1 = b1`.
The head moves to the next card.

```
-------------------------------
|r1   |b1   |draw2|r0   |draw2| (Tape)
-------------------------------
  55    56    57  ^ 58    59
-------------------------------
|y101 |b12  |g0   |b1   |draw2| (Stack)
-------------------------------

-------------------------------
|r1   |b1   |draw2|r0   |draw2| (Tape)
-------------------------------
  55    56    57    58  ^ 59
-------------------------------
|y108 |r108 |y101 |b12  |b1   | (Stack)
-------------------------------

```

## Trademark Notes

According to the back of my UNO deck, Mattel, Inc. owns the "UNO" trademark.
This project is not associated with Mattel in any way.

