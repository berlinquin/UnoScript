%option noyywrap

%{
#include "uno.h"
%}

%%

[rygb][0-9] { return COLOR; }
wild    { return WILD; }
skip    { return SKIP; }
reverse { return REVERSE; }
draw2   { return DRAW2; }
draw4   { return DRAW4; }

%%
