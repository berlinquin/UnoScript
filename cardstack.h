#ifndef CARDSTACK_H
#define CARDSTACK_H

#include <deque>
#include "uno.h"

/*
 * An adapter around std::deque which behaves as a stack.
 * It returns a WILD card if pop() is called on an empty stack.
 */
class CardStack
{
public:
   CardStack();
   ~CardStack();

   void push(const card_t& card);
   card_t top();
   void top(card_t *cards[], int num);
   void pop();

private:
   std::deque<card_t> m_deque;
};

#endif // CARDSTACK_H
