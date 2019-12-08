#include <iostream>
#include <vector>
#include <stack>

#include "uno.h"

/*
 * Anonymous namespace to hold global variables
 */
namespace {
   // Hold the program source
   std::vector<card_t> tape;

   // Set head over the first item on tape
   int head = 0;

   // The program stack
   std::stack<card_t> stack;

   // The different modes the head can be in
   enum { READ, SCAN } mode;

   // The jump direction
   enum { LEFT, RIGHT } seek_direction;
};

void process_symbol(card_t& read, card_t& top);


int main(int argc, char *argv[])
{
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
         // Need to read in the next symbol
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
            top_card = stack.top();
         }
         process_symbol(next_card, top_card);
      }
      else if (mode == SCAN)
      {
         // Check to see if match found
      }

   }

   return 0;
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
