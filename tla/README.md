# Formal Specification with TLA+

This directory contains a formal specification of UnoScript written in the TLA+ specification language.

## Goals

The specifications were written with these goals in mind:
- Formalize the [specification document](../specs.md).
  The TLA+ specs should express the same language as the specification document,
  but in a more rigorous and precise manner.
- Verify basic properties of UnoScript.
  This includes type-safety of operations on the stack and memory.
- Give me a practical way to learn TLA+.
  TLA+ really interests me, so this is a way to try it out in a familiar context.

## Structure

The core data structures of UnoScript are the **tape** and the **stack**.
The tape holds the contents of the program as an immutable sequence of Uno cards.
The stack holds the working data of a running program, given as a mutable sequence of Uno cards.

Starting out, I found it easier to write specifications for the individual data structures.
- *TapeSpec.tla* contains a formal specification of the tape
- *StackSpec.tla* contains a formal specification of the stack

Later, I combined these into a single specification, found in *UnoScript.tla*.

## Checking the Specification

To verify these specifications, you'll need to have the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) installed.
With the Toolbox installed, you can open the specification files and create a model to check.
The model will require you to set values for the constants
and expressions for the next-state function and invariants.
