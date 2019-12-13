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

   // True if inside the scope of a conditional
   bool conditional;

   // Which conditional and which branch is being executed
   enum { IF, IF_BRANCH, ELSE_BRANCH } conditional_mode;

   // True if head should seek to the right
   bool seek_right;

   // Markers for the most recent conditional
   card_t else_marker, endif;

   // Marker for skip and reverse
   card_t marker;
};

void process_symbol(card_t& read, card_t& top);

void drawTwo(card_t operation);
void drawFour(card_t operation);

bool matches(const card_t& a, card_t& b);

int main(int argc, char *argv[])
{
   // Set head over the first item on tape, initialize mode and seek direction
   head = 0;
   mode = READ;
   conditional = false;
   seek_right = true;
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
         // If inside a conditional, check to see if at the end of a branch
         if (conditional)
         {
            if (conditional_mode == IF && matches(next_card, endif))
            {
               head++;
               conditional = false;
               continue;
            }
            else if (conditional_mode == IF_BRANCH && matches(next_card, else_marker))
            {
               head++;
               mode = SCAN;
               continue;
            }
            else if (conditional_mode == ELSE_BRANCH && matches(next_card, endif))
            {
               head++;
               conditional = false;
               mode = READ;
               continue;
            }
         }

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
                  drawFour(top_card);
                  break;
            }
         }
         else if (next_card.type == WILD)
         {
            stack.push(top_card);
            if (top_card.type == COLOR)
            {
               stack.push(next_card);
            }
         }
         else if (next_card.type == SKIP || next_card.type == REVERSE)
         {
            // if type REVERSE, flip the seek direction
            seek_right ^= next_card.type == REVERSE;
            switch(top_card.type)
            {
               case COLOR:
               case WILD: // use top card as marker
                  mode = SCAN;
                  marker = top_card;
                  stack.push(top_card);
                  stack.push(next_card);
                  break;
               case DRAW2:
               case DRAW4: // no-op, keep operator on stack
                  stack.push(top_card);
                  break;
            }
         }
         else if (next_card.type == DRAW2 || next_card.type == DRAW4)
         {
            switch(top_card.type)
            {
               case COLOR:
               case WILD: // push operator onto stack
                  stack.push(top_card);
                  stack.push(next_card);
                  break;
               case DRAW2:
               case DRAW4: // replace operator on stack
                  stack.push(next_card);
                  break;
            }
         }
         // Increment the head for next iteration
         head++;
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
            conditional = true;
            conditional_mode = IF;
            endif = a;
            if (b.digit)
            {
               mode = READ;
            }
            else
            {
               mode = SCAN;
            }
            break;
      }
   }
}

/*
 * Perform the given operation on the top four values of stack
 */
void drawFour(card_t operation)
{
   // Read top four symbols from stack
   card_t top_four[4];
   for (int i = 0; i < 4; i++)
   {
      top_four[i] = stack.top();
      stack.pop();
   }

   if (operation.digit == 1)
   {
     switch (operation.color)
     {
        case RED: // 2Swap
          stack.push(top_four[1]);
          stack.push(top_four[0]);
          stack.push(top_four[3]);
          stack.push(top_four[2]);
          break;
        case YELLOW: // 2Dup
          stack.push(top_four[3]);
          stack.push(top_four[2]);
          stack.push(top_four[1]);
          stack.push(top_four[0]);
          stack.push(top_four[1]);
          stack.push(top_four[0]);
          break;
        case GREEN: // 2Over
          stack.push(top_four[3]);
          stack.push(top_four[2]);
          stack.push(top_four[1]);
          stack.push(top_four[0]);
          stack.push(top_four[3]);
          stack.push(top_four[2]);
          break;
        case BLUE: // 2Drop
          stack.push(top_four[3]);
          stack.push(top_four[2]);
          break;
     }
   }
   else if (operation.digit == 2)
   {
      switch(operation.color)
      {
         case RED: // Rot
            stack.push(top_four[3]);
            stack.push(top_four[1]);
            stack.push(top_four[0]);
            stack.push(top_four[2]);
            break;
         case BLUE: // if/else/endif
            stack.push(top_four[3]);
            conditional = true;
            else_marker = top_four[1];
            endif = top_four[0];
            if (top_four[2].digit)
            {
               mode = READ;
               conditional_mode = IF_BRANCH;
            }
            else
            {
               mode = SCAN;
               conditional_mode = ELSE_BRANCH;
            }
            break;
      }
   }
}

bool matches(const card_t& a, card_t& b)
{
   return (a.type == b.type) && (a.color == b.color) && (a.digit == b.digit);
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
