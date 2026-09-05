%{
#include<stdio.h>
#include<string.h>
#include"y.tab.h"
extern int yylineno;
int prev_lineno = 1;

char buffer[10240]="";
void append(const char* str){
        if (strlen(buffer)+strlen(str)<10240){
                strcat(buffer,str);
        }
}

static int _token_col = 1;

static const char* token_name(int tok) {
    switch (tok) {
        case DEFAULT:   return "KEYWORD(def)";
        case BREAK:     return "KEYWORD(exit)";
        case CONTINUE:  return "KEYWORD(skip)";
        case ENUM:      return "KEYWORD(enum)";
        case PTRTYPE:   return "TYPE(@ptr)";
        case ADDROF:    return "KEYWORD(ref)";
        case DEREF:     return "KEYWORD(deref)";
        case SHORT:     return "TYPE(@short)";
        case LONG:      return "TYPE(@long)";
        case DOUBLE:    return "TYPE(@double)";
        case INPUT:     return "KEYWORD(input)";
        case BAND:      return "OP(bitand)";
        case BOR:       return "OP(bitor)";
        case BXOR:      return "OP(bitxor)";
        case BNOT:      return "OP(bitnot)";
        case LSHIFT:    return "OP(lshift)";
        case RSHIFT:    return "OP(rshift)";
        case INC:       return "OP(++)";
        case DEC:       return "OP(--)";
        case PASN:      return "OP(+=)";
        case MASN:      return "OP(-=)";
        case SASN:      return "OP(*=)";
        case DASN:      return "OP(/=)";
        case MODASN:    return "OP(%=)";
        case BANDASN:   return "OP(bitand=)";
        case BORASN:    return "OP(bitor=)";
        case BXORASN:   return "OP(bitxor=)";
        case LSHIFTASN: return "OP(lshift=)";
        case RSHIFTASN: return "OP(rshift=)";
        case AND:       return "OP(and)";
        case OR:        return "OP(or)";
        case EQ:        return "OP(==)";
        case NE:        return "OP(!=)";
        case LT:        return "OP(<)";
        case GT:        return "OP(>)";
        case LE:        return "OP(<=)";
        case GE:        return "OP(>=)";
        case TR:        return "LITERAL(true)";
        case FL:        return "LITERAL(false)";
        case IF:        return "KEYWORD(if/when)";
        case ELSE:      return "KEYWORD(else/otherwise)";
        case INT:       return "TYPE(@int)";
        case VOID:      return "TYPE(@void)";
        case FLOAT:     return "TYPE(@float)";
        case CHAR:      return "TYPE(@char)";
        case FUNCTION:  return "KEYWORD(func)";
        case RETURN:    return "KEYWORD(ret)";
        case CALL:      return "KEYWORD(call)";
        case PRINT:     return "KEYWORD(show)";
        case SIZEOF:    return "KEYWORD(getsizeof)";
        case ABS:       return "BUILTIN(abs)";
        case MIN:       return "BUILTIN(min)";
        case MAX:       return "BUILTIN(max)";
        case WHILE:     return "KEYWORD(loop)";
        case DO:        return "KEYWORD(repeat)";
        case FOR:       return "KEYWORD(iterate)";
        case SWITCH:    return "KEYWORD(choose)";
        case CASE:      return "KEYWORD(option)";
        case CONST:     return "KEYWORD(fixed)";
        case STRING:    return "LITERAL(string)";
        case NUM:       return "LITERAL(number)";
        case CHARR:     return "LITERAL(char)";
        case IDEN:      return "IDENTIFIER";
        case MEOF:      return "EOF";
        /* ── Heap allocation ── */
        case ALLOC:     return "BUILTIN(alloc)";
        case CALLOC:    return "BUILTIN(calloc)";
        case REALLOC:   return "BUILTIN(realloc)";
        case HFREE:     return "BUILTIN(free)";
        case NULLPTR:   return "LITERAL(null)";
        default: {
            static char buf[16];
            if (tok > 32 && tok < 127)
                snprintf(buf, sizeof(buf), "PUNCT('%c')", (char)tok);
            else
                snprintf(buf, sizeof(buf), "TOKEN(%d)", tok);
            return buf;
        }
    }
}

static int _pretty_return(int tok, const char* lexeme, int line) {
    static int trace = -1;
    static int header_printed = 0;
    if (trace < 0) {
        const char* env = getenv("LEXER_TOKEN_TRACE");
        trace = (env && env[0] == '1') ? 1 : 0;
    }
    if (trace) {
        /* Print column header once at the very start */
        if (!header_printed) {
            fprintf(stderr, "%-12s %-23s %s\n",
                    "[LINE:COL]", "TOKEN TYPE", "LEXEME");
            fprintf(stderr, "%-12s %-23s %s\n",
                    "----------", "----------------------", "------");
            header_printed = 1;
        }
        char safe[256];
        int  si = 0;
        for (const char* p = lexeme; *p && si < (int)sizeof(safe)-4; p++) {
            if      (*p == '\n') { safe[si++]='\\'; safe[si++]='n'; }
            else if (*p == '\t') { safe[si++]='\\'; safe[si++]='t'; }
            else                   safe[si++] = *p;
        }
        safe[si] = '\0';
        
        char loc_buf[32];
        snprintf(loc_buf, sizeof(loc_buf), "[%d:%d]", line, _token_col);
        fprintf(stderr, "%-12s %-23s \"%s\"\n",
                loc_buf, token_name(tok), safe);
    }
    for (const char* p = lexeme; *p; p++) {
        if (*p == '\n') _token_col = 1;
        else            _token_col++;
    }
    return tok;
}

#define TOK(t)  return _pretty_return((t), yytext, yylineno)
%}

/* Enable line number counting */
%option yylineno



iden [[:alpha:]_][[:alnum:]_]*
num [[:digit:]]+\.?[[:digit:]]*
num2 [[:digit:]]*\.?[[:digit:]]+
ws [\t ]
%%
"#".*                      {}
"'''"([^']|'[^']|''[^'])*"'''"  {}  // ''' multi-line comment '''
"\"\"\""([^"]|"[^"]|""[^"])*"\"\"\""  {}  // """ multi-line comment """
"def"   {append(yytext);strcpy(yylval.str,yytext);TOK(DEFAULT);}
"exit"     {append(yytext);strcpy(yylval.str,yytext);TOK(BREAK);}
"skip"  {append(yytext);strcpy(yylval.str,yytext);TOK(CONTINUE);}
enum  { append(yytext); strcpy(yylval.str, yytext); TOK(ENUM); }

@ptr    { append(yytext); strcpy(yylval.str, yytext); TOK(PTRTYPE); }
ref     { append(yytext); strcpy(yylval.str, yytext); TOK(ADDROF); }
deref   { append(yytext); strcpy(yylval.str, yytext); TOK(DEREF); }

@short  {append(yytext);strcpy(yylval.str,yytext);TOK(SHORT);}
@long   {append(yytext);strcpy(yylval.str,yytext);TOK(LONG);}
@double {append(yytext);strcpy(yylval.str,yytext);TOK(DOUBLE);}
input {append(yytext);strcpy(yylval.str,yytext);TOK(INPUT);}
"begin" {append(yytext);TOK('{');}
"end"   {append(yytext);TOK('}');}
"bitand"  {append(yytext);strcpy(yylval.str,yytext);TOK(BAND);}
"bitor"  {append(yytext);strcpy(yylval.str,yytext);TOK(BOR);}
"bitxor"  {append(yytext);strcpy(yylval.str,yytext);TOK(BXOR);}
"bitnot"  {append(yytext);strcpy(yylval.str,yytext);TOK(BNOT);}
"lshift" {append(yytext);strcpy(yylval.str,yytext);TOK(LSHIFT);}
"rshift" {append(yytext);strcpy(yylval.str,yytext);TOK(RSHIFT);}
"++" {append(yytext);strcpy(yylval.str,yytext);TOK(INC);}
"--" {append(yytext);strcpy(yylval.str,yytext);TOK(DEC);}
"+=" {append(yytext);strcpy(yylval.str,yytext);TOK(PASN);}
"-=" {append(yytext);strcpy(yylval.str,yytext);TOK(MASN);}
"*=" {append(yytext);strcpy(yylval.str,yytext);TOK(SASN);}
"/=" {append(yytext);strcpy(yylval.str,yytext);TOK(DASN);}
"%=" {append(yytext);strcpy(yylval.str,yytext);TOK(MODASN);}
"bitand=" {append(yytext);strcpy(yylval.str,yytext);TOK(BANDASN);}
"bitor=" {append(yytext);strcpy(yylval.str,yytext);TOK(BORASN);}
"bitxor=" {append(yytext);strcpy(yylval.str,yytext);TOK(BXORASN);}
"lshift=" {append(yytext);strcpy(yylval.str,yytext);TOK(LSHIFTASN);}
"rshift=" {append(yytext);strcpy(yylval.str,yytext);TOK(RSHIFTASN);}
"and" {append(yytext);strcpy(yylval.str,"&&");TOK(AND);}
"or"  {append(yytext);strcpy(yylval.str,"||");TOK(OR);}
"not" {append(yytext);TOK('!');}
"==" {append(yytext);strcpy(yylval.str,"==");TOK(EQ);}
"!=" {append(yytext);strcpy(yylval.str,"!=");TOK(NE);}
"<" {append(yytext);strcpy(yylval.str,"<");TOK(LT);}
">" {append(yytext);strcpy(yylval.str,">");TOK(GT);}
"<=" {append(yytext);strcpy(yylval.str,"<=");TOK(LE);}
">=" {append(yytext);strcpy(yylval.str,">=");TOK(GE);}
"eq" {append(yytext);strcpy(yylval.str,"==");TOK(EQ);}
"ne" {append(yytext);strcpy(yylval.str,"!=");TOK(NE);}
"lt" {append(yytext);strcpy(yylval.str,"<");TOK(LT);}
"gt" {append(yytext);strcpy(yylval.str,">");TOK(GT);}
"le" {append(yytext);strcpy(yylval.str,"<=");TOK(LE);}
"ge" {append(yytext);strcpy(yylval.str,">=");TOK(GE);}
true {append(yytext);strcpy(yylval.str,yytext);TOK(TR);}
false {append(yytext);strcpy(yylval.str,yytext);TOK(FL);}
if   {append(yytext);strcpy(yylval.str,yytext);TOK(IF);}
else {append(yytext);strcpy(yylval.str,yytext);TOK(ELSE);}
@int {append(yytext);strcpy(yylval.str,yytext);TOK(INT);}
@void {append(yytext);strcpy(yylval.str,yytext);TOK(VOID);}
@float {append(yytext);strcpy(yylval.str,yytext);TOK(FLOAT);}
@char {append(yytext);strcpy(yylval.str,yytext);TOK(CHAR);}
func {append(yytext);strcpy(yylval.str,yytext);TOK(FUNCTION);}
ret  {append(yytext);strcpy(yylval.str,yytext);TOK(RETURN);}
call     {append(yytext);strcpy(yylval.str,yytext);TOK(CALL);}
show {append(yytext);strcpy(yylval.str,yytext);TOK(PRINT);}
"getsizeof" {append(yytext);TOK(SIZEOF);}
"abs"   {append(yytext);strcpy(yylval.str,yytext);TOK(ABS);}
"min"   {append(yytext);strcpy(yylval.str,yytext);TOK(MIN);}
"max"   {append(yytext);strcpy(yylval.str,yytext);TOK(MAX);}
loop {append(yytext);strcpy(yylval.str,yytext);TOK(WHILE);}
repeat {append(yytext);strcpy(yylval.str,yytext);TOK(DO);}
is    {append(yytext);TOK('=');}
iterate  {append(yytext);strcpy(yylval.str,yytext);TOK(FOR);}
choose   {append(yytext);strcpy(yylval.str,yytext);TOK(SWITCH);}
option   {append(yytext);strcpy(yylval.str,yytext);TOK(CASE);}
when   {append(yytext);strcpy(yylval.str,yytext);TOK(IF);}
otherwise {append(yytext);strcpy(yylval.str,yytext);TOK(ELSE);}
fixed {append(yytext);strcpy(yylval.str,yytext);TOK(CONST);}

"alloc"   { append(yytext); strcpy(yylval.str, yytext); TOK(ALLOC);   }
"calloc"  { append(yytext); strcpy(yylval.str, yytext); TOK(CALLOC);  }
"realloc" { append(yytext); strcpy(yylval.str, yytext); TOK(REALLOC); }
"free"    { append(yytext); strcpy(yylval.str, yytext); TOK(HFREE);   }
"release" { append(yytext); strcpy(yylval.str, yytext); TOK(HFREE);   }
"null"    { append(yytext); strcpy(yylval.str, "0");    TOK(NULLPTR);  }
\"([^\"]|\\\")*\"  {
    append(yytext);
    strcpy(yylval.str, yytext);  
    TOK(STRING);
}

hex[0-9a-fA-F]+  {
    append(yytext);
    long val = strtol(yytext+3, NULL, 16);
    sprintf(yylval.str, "%ld", val);
    TOK(NUM);
}

oct[0-7]+  {
    append(yytext);
    long val = strtol(yytext+3, NULL, 8);
    sprintf(yylval.str, "%ld", val);
    TOK(NUM);
}

bin[01]+  {
    append(yytext);
    long val = strtol(yytext+3, NULL, 2);
    sprintf(yylval.str, "%ld", val);
    TOK(NUM);
}
({num}|{num2}) {append(yytext);strcpy(yylval.str,yytext);TOK(NUM);}
{iden} {append(yytext);strcpy(yylval.str,yytext);TOK(IDEN);}
\n {append(yytext); prev_lineno = yylineno - 1; }
{ws} {append(yytext);}
<<EOF>> {TOK(MEOF);}
'\\n' {
    append(yytext);
    strcpy(yylval.str, "'\\n'");  
    TOK(CHARR);
}
'\\t' {
    append(yytext);
    strcpy(yylval.str, "'\\t'");  
    TOK(CHARR);
}
'\\0' {
    append(yytext);
    strcpy(yylval.str, "'\\0'");  
    TOK(CHARR);
}
'[^']' { 
    append(yytext);  
    strcpy(yylval.str, yytext); 
    TOK(CHARR); 
}
. {append(yytext);strcpy(yylval.str,yytext);TOK((unsigned char)yytext[0]);}
%%
