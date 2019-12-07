#ifndef UNO_H
#define UNO_H

/*
 * Declare yylex method which will be implemented by flex
 */
extern int yylex(void);

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
 * The valid color values for a color card
 */
typedef enum
{
   RED,
   YELLOW,
   GREEN,
   BLUE,
} color_t;

/*
 * Hold the color and value of a color card
 */
typedef struct
{
   color_t color;
   int digit;
} color_card_t;

/*
 * Represent a card which consists of a card type and additional data based on card type
 */
typedef struct
{
   card_type_t card;
   union {
      color_card_t color_card;
   };
} card_t;

#endif // UNO_H
