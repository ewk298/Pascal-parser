%{    /* lexasu.l -- sample lex specification      20 Jul 99; 19 Jul 01 */
      /* Aho, Sethi, Ullman book example, adapted by G. Novak  */

#define LT 8        /* Example of use:                                       */
#define LE 9        /* lex ~cs375/lexasu.l       Use lex to compile lexasu.l */
#define EQ 6        /* cc lex.yy.c -ll             Compile lex output with C */
#define NE 7        /* a.out                       Execute C output          */
#define GT 11       /* if switch then 3.14 else 4  Test data                 */
#define GE 10       /* ^D                          Control-D for EOF to stop */
#define ID      3
#define NUMBER  5
#define OP      -1   /* to avoid returning 0 */
/*reserved words*/
#define ARRAY		1
#define BEGINBEGIN	2
#define CASE		3
#define CONST		4
#define DO			5
#define DOWNTO		6
#define ELSE		7
#define ENDEND		8
#define	FILEFILE	9
#define FOR			10
#define FUNCTION	11
#define GOTO		12
#define IF			13
#define LABEL		14
#define NIL			15
#define OF			16
#define PACKED		17
#define	PROCEDURE	18
#define	PROGRAM		19
#define	RECORD		20
#define	REPEAT		21
#define	SET			22
#define	THEN		23
#define	TO			24
#define TYPE		25
#define	UNTIL		26
#define	VAR			27
#define	WHILE		28
#define	WITH		29
/*end reserved words*/


int yylval;

%}
        /* regular definitions */

delim   [ \t\n]
ws      {delim}+
letter  [A-Za-z]
digit   [0-9]
id      {letter}({letter}|{digit})*
number  {digit}+(\.{digit}+)?(E[+\-]?{digit}+)?

%%

{ws}     	{ /* no action and no return */ }
array 		{ return (ARRAY); }
begin		{ return (BEGINBEGIN); }
case		{return(CASE);}
{id}     	{ yylval = install_id(); return(ID); }
{number} 	{ yylval = install_num(); return(NUMBER); }
"<"      	{ yylval = LT; return(OP); }
"<="     	{ yylval = LE; return(OP); }
"="      	{ yylval = EQ; return(OP); }
"<>"     	{ yylval = NE; return(OP); }
">"      	{ yylval = GT; return(OP); }
">="     	{ yylval = GE; return(OP); }

%%       /* C functions */

install_id() {  printf("id  %10s   n = %4d\n",yytext,yyleng);  }

install_num() {  printf("num %10s   n = %4d\n",yytext,yyleng);  }

yywrap() {  return(1);  }   /* lex seems to need this. */

main()          /* Call yylex repeatedly to test */
  { int res, done;
    done = 0;
    while (done == 0)
      { res = yylex();
        if (res != 0)
           {
            printf("yylex result = %4d\n", res);
           }
           else done = 1;
      }
    exit(0);
    }
