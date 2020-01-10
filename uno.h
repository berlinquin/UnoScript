#ifndef UNO_H
#define UNO_H

/*
 * The different types of cards
 */
typedef enum
{
   COLOR = 1, // start at 1 since flex returns 0 on EOF
   WILD,
   SKIP,
   REVERSE,
   DRAW2,
   DRAW4
} card_type_t;

/*
 * The valid color values
 */
typedef enum
{
   RED,
   YELLOW,
   GREEN,
   BLUE,
} color_t;

/*
 * Represent a card which consists of a card type and optional data based on card type
 */
typedef struct
{
   card_type_t type;
   color_t color;
   int digit;
} card_t;

/*
 * Write a string representation of card to str, a buffer of the given length
 */
void cardToString(card_t card, char *str, int len);

/*
 * Declare yylex method which will be implemented by flex
 */
extern int yylex(card_t*);

#endif // UNO_H
