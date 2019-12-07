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
   COLOR, 
   WILD,
   SKIP,
   REVERSE,
   DRAW2,
   DRAW4
} card_t;

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

#endif // UNO_H
