/*Compile with: flex scanner.l -o scanner.c; gcc scanner.c -o scanner*/
%option noyywrap
%option noinput
%option nounput
%x IN_COMMENT
%{
#include <stdio.h>
%}
%%
<INITIAL>{
"/*"          BEGIN(IN_COMMENT);
"//".*\n      printf("line comment\n");
[ \n\t]       ; // eat whitespace
\-            printf("minus\n");
"+"           printf("plus\n");
"*"           printf("times\n");
"/"           printf("divide\n");
"("           printf("brace open\n");
")"           printf("brace close\n");
[+-]?[0-9]+   printf("number: %d\n", atoi(yytext));
[_a-zA-Z][_a-zA-Z0-9-]* printf("ident: %s\n", yytext);
.             printf("illegal character: '%c' (%02x)\n", yytext[0], yytext[0]);
}
<IN_COMMENT>{
"*/"          BEGIN(INITIAL);
[^*\n]+       ; // eat comment in chunks
"*"           ; // eat the lone star
\n            yylineno++;
}
%%
int main (void)
{
	return yylex();
}
