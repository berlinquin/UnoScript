default: uno.h uno.cpp uno.l
	lex uno.l
	g++ -g lex.yy.c uno.cpp -o ui

clean:
	rm lex.yy.c
