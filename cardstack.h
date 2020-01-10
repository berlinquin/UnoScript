#ifndef CARDSTACK_H
#define CARDSTACK_H

#include <vector>
#include <deque>
#include "uno.h"

/*
 * An adapter around std::deque which behaves as a stack.
 * It returns a WILD card if top() is called on an empty stack.
 */
class CardStack
{
public:
   CardStack();
   ~CardStack();

   void push(const card_t& card);
   card_t top();
   std::vector<card_t> top(int num);
   void pop();

private:
   std::deque<card_t> m_deque;
};

#endif // CARDSTACK_H
