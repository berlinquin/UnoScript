#include <vector>
#include <stack>

#include "uno.h"

int main(int argc, char *argv[])
{
   // Hold the program source
   std::vector<card_t> tape;

   // Set head over the first item on tape
   int head = 0;

   // The program stack
   std::stack<card_t> stack;

   // The different modes the head can be in
   enum { READ, SCAN } mode;
   mode = READ;

   // The jump direction
   enum { LEFT, RIGHT } seek_direction;
   seek_direction = RIGHT;

   card_t next_card;
   /*
    * Invariants:
    * head >= 0
    */
   while (true)
   {
      // Read the symbol under the head
      if (head == tape.size())
      {
         // Need to read in the next symbol
         if (yylex(&next_card == 0);
         {
            printf("Reached end of input\n");
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
            top_card = stack.pop();
         }
      }

   }

   return 0;
}
