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

   while (yylex() != 0)
   {

   }

   return 0;
}
