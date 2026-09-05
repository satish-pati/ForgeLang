CC = gcc
CFLAGS = -w

all: parser_unoptimized parser_optimized

parser_unoptimized: parser_unoptimized.y lexer.l
	flex lexer.l
	yacc -d parser_unoptimized.y
	$(CC) $(CFLAGS) y.tab.c lex.yy.c -lfl -o parser_unoptimized

parser_optimized: parser_optimized.y lexer.l
	flex lexer.l
	yacc -d parser_optimized.y
	$(CC) $(CFLAGS) y.tab.c lex.yy.c -lfl -o parser_optimized

clean:
	rm -f parser_unoptimized parser_optimized output.s y.tab.c y.tab.h lex.yy.c \
	*.html *.tac *.dot *.png *.txt *.json generated.py