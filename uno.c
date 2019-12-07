#include "uno.h"

int main(int argc, char *argv[])
{
   while (yylex() != 0);
   return 0;
}
