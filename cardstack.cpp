#include <deque>
#include "uno.h"
#include "cardstack.h"

/*
 * Empty constructor
 */
CardStack::CardStack()
{
}

/*
 * Empty destructor
 */
CardStack::~CardStack()
{
}

void CardStack::push(const card_t& card)
{
   m_deque.push_back(card);
}

card_t CardStack::top()
{
   card_t wild;
   wild.type = WILD;
   if (m_deque.empty())
   {
      return wild;
   }
   else
   {
      return m_deque.back();
   }
}

void CardStack::pop()
{
   if (!m_deque.empty())
   {
      m_deque.pop_back();
   }
}

void CardStack::print()
{
   int len = std::min(5, (int) m_deque.size());

   // Return early if stack is empty
   if (len == 0)
   {
      printf("[Empty stack]\n");
      return;
   }

   // Print a top row of dashes
   int num_dashes = (len*6)+1;
   for (int i = 0; i < num_dashes; i++)
   {
      printf("-");
   }
   printf("\n");

   // Print each card in top_five
   std::deque<card_t>::reverse_iterator it = m_deque.rbegin();
   int i = 0;
   char str[6];
   while (i < len && it != m_deque.rend())
   {
      cardToString(*it, str, 6);
      printf("|%-5s", str);
      // Increment counters
      ++it;
      ++i;
   }
   printf("|\n");

   // Print a bottom row of dashes
   for (int i = 0; i < num_dashes; i++)
   {
      printf("-");
   }
   printf("\n");
}

