#include <deque>
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

void CardStack::top(card_t cards[], int num)
{
   std::deque<card_t>::reverse_iterator it = m_deque.rbegin();
   int i = 0;
   int top_of_stack = m_deque.size() - 1;
   while (i < num && it != m_deque.rend())
   {
      cards[i] = m_deque.at(top_of_stack - i);
      i++;
   }
}


void CardStack::pop()
{
   if (!m_deque.empty())
   {
      m_deque.pop_back();
   }
}
