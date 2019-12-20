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
   m_stack.push(card);
}

card_t CardStack::top()
{
   card_t wild;
   wild.type = WILD;
   if (m_stack.empty())
   {
      return wild;
   }
   else
   {
      return m_stack.top();
   }
}

void CardStack::pop()
{
   if (!m_stack.empty())
   {
      m_stack.pop();
   }
}
