%option noyywrap

%{
#include "uno.h"

// define yylex() to accept a card_t out parameter
#define YY_DECL int yylex(card_t *card)

// method to return a card_t struct from card_type_t
card_t build_card(card_type_t);
%}

%%

[rygb][0-9] { 
   card->type = COLOR;
   switch (yytext[0])
   {
      case 'r': card->color = RED; break;
      case 'y': card->color = YELLOW; break;
      case 'g': card->color = GREEN; break;
      case 'b': card->color = BLUE; break;
   }
   card->digit = yytext[1] - '0';
   return COLOR;
}
wild    { *card = build_card(WILD); return WILD; }
skip    { *card = build_card(SKIP); return SKIP; }
reverse { *card = build_card(REVERSE); return REVERSE; }
draw2   { *card = build_card(DRAW2); return DRAW2; }
draw4   { *card = build_card(DRAW4); return DRAW4; }

[ \n\t] { /* ignore whitespace */ }

%%

card_t build_card(card_type_t card_type)
{
   card_t card;
   card.type = card_type;
   return card;
}
