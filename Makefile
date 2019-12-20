default: uno.h uno.cpp uno.l cardstack.h cardstack.cpp
	lex uno.l
	g++ lex.yy.c uno.cpp cardstack.cpp -o ui

clean:
	rm lex.yy.c
