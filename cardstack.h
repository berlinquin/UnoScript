#ifndef CARDSTACK_H
#define CARDSTACK_H

#include <stack>
#include "uno.h"

/*
 * A simple adapter around std::stack that returns a WILD card
 * if pop() is called on an empty stack.
 */
class CardStack
{
public:
   CardStack();
   ~CardStack();

   void push(const card_t& card);
   card_t top();
   void pop();

private:
   std::stack<card_t> m_stack;
};

#endif // CARDSTACK_H
