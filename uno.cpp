#include <iostream>
#include <vector>
#include <stack>

#include "uno.h"

/*
 * Anonymous namespace to hold global variables
 */
namespace {
   // Program source
   std::vector<card_t> tape;

   // Position of the head on tape
   int head;

   // Program stack
   std::stack<card_t> stack;

   // Program random-access storage
   card_t registers[4][10];

   // The different modes the head can be in
   enum { READ, SCAN } mode;

   // The jump direction
   enum { LEFT, RIGHT } seek_direction;
};

void process_symbol(card_t& read, card_t& top);

void drawTwo(card_t operation);

int main(int argc, char *argv[])
{
   // Set head over the first item on tape, initialize mode and seek direction
   head = 0;
   mode = READ;
   seek_direction = RIGHT;
   /*
    * Invariants:
    * head >= 0
    */
   card_t next_card;
   while (true)
   {
      // Read the symbol under the head
      if (head == tape.size())
      {
         // Read in the next symbol
         if (yylex(&next_card) == 0);
         {
            std::cout << "Reached end of input";
            break;
         }
         tape.push_back(next_card);
      }
      else
      {
         // Symbol already in memory
         next_card = tape.at(head);
      }

      // Handle the card based on the current mode
      if (mode == READ)
      {
         // Examine the top of the stack
         card_t top_card;
         if (stack.empty())
         {
            top_card.type = WILD;
         }
         else
         {
            // Get a copy of the top card and pop from stack
            top_card = stack.top();
            stack.pop();
         }

         // Look at the symbol under the head, then the top of the stack
         if (next_card.type == COLOR)
         {
            switch (top_card.type)
            {
               case COLOR: 
                  if (next_card.color == top_card.color)
                  {
                     top_card.digit = top_card.digit * 10 + next_card.digit;
                     stack.push(top_card);
                  }
                  else
                  {
                     stack.push(top_card);
                     stack.push(next_card);
                  }
                  break;
               case WILD:
                  stack.push(next_card);
                  break;
               case DRAW2:
                  // based on value of next_card, do operation on top two symbols
                  drawTwo(top_card);
                  break;
               case DRAW4:
                  // based on value of next_card, do operation on top four symbols
                  break;
            }
         }
         else if (next_card.type == WILD)
         {
         }
         else if (next_card.type == SKIP)
         {
         }
         else if (next_card.type == REVERSE)
         {
         }
         else if (next_card.type == DRAW2)
         {
         }
         else if (next_card.type == DRAW4)
         {
         }
      }
      else if (mode == SCAN)
      {
         // Check to see if match found
      }

   }

   return 0;
}

/*
 * Perform the given operation on the top two values of stack
 */
void drawTwo(card_t operation)
{
   // Read top two symbols from stack
   card_t a = stack.top();
   stack.pop();
   card_t b = stack.top();
   stack.pop();
   
   if (operation.digit == 0)
   {
     switch (operation.color)
     {
        case RED:
          b.digit += a.digit; break;
        case YELLOW:
          b.digit -= a.digit; break;
        case GREEN:
          b.digit *= a.digit; break;
        case BLUE:
          b.digit /= a.digit; break;
     }
     b.color = a.color;
     stack.push(b);
   }
   else if (operation.digit == 1)
   {
      switch (operation.color)
      {
         case RED:
            stack.push(a);
            stack.push(b);
            break;
         case YELLOW:
            stack.push(b);
            stack.push(a);
            stack.push(a);
            break;
         case GREEN:
            stack.push(b);
            stack.push(a);
            stack.push(b);
            break;
         case BLUE:
            stack.push(b);
            break;
      }
   }
   else if (operation.digit == 2)
   {
      switch (operation.color)
      {
         case RED: 
            registers[a.color][a.digit] = b;
            stack.push(b);
            break;
         case YELLOW:
            stack.push(b);
            stack.push(registers[a.color][a.digit]);
            break;
         case GREEN:
            printf("%c", a.digit);
            stack.push(b);
            stack.push(a);
            break;
         case BLUE:
            break;
      }
   }
}

int read_symbol_under_head(card_t *card)
{
   return 0;
}

/*
 * Update the intepreter state,
 * where read is the symbol currently under the head
 * and top is the symbol at the top of the stack
 */
void process_symbol(card_t& read, card_t& top)
{

}
