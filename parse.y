%{     /* pars1.y    Pascal Parser      Gordon S. Novak Jr.  ; 30 Jul 13   */

/* Copyright (c) 2013 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* 14 Feb 01; 01 Oct 04; 02 Mar 07; 27 Feb 08; 24 Jul 09; 02 Aug 12 */

/*
; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, see <http://www.gnu.org/licenses/>.
  */


/* NOTE:   Copy your lexan.l lexical analyzer to this directory.      */

       /* To use:
                     make pars1y              has 1 shift/reduce conflict
                     pars1y                   execute the parser
                     i:=j .
                     ^D                       control-D to end input

                     pars1y                   execute the parser
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.
                     ^D

                     pars1y                   execute the parser
                     if x+y then if y+z then i:=j else k:=2.
                     ^D

           You may copy pars1.y to be parse.y and extend it for your
           assignment.  Then use   make parser   as above.
        */

        /* Yacc reports 1 shift/reduce conflict, due to the ELSE part of
           the IF statement, but Yacc's default resolves it in the right way.*/

#include <stdio.h>
#include <ctype.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"

        /* define the type of the Yacc stack element to be TOKEN */

#define YYSTYPE TOKEN

TOKEN parseresult;

%}

/* Order of tokens corresponds to tokendefs.c; do not change */

%token IDENTIFIER STRING NUMBER   /* token types */

%token PLUS MINUS TIMES DIVIDE    /* Operators */
%token ASSIGN EQ NE LT LE GE GT POINT DOT AND OR NOT DIV MOD IN

%token COMMA                      /* Delimiters */
%token SEMICOLON COLON LPAREN RPAREN LBRACKET RBRACKET DOTDOT

%token ARRAY BEGINBEGIN           /* Lex uses BEGIN */
%token CASE CONST DO DOWNTO ELSE END FILEFILE FOR FUNCTION GOTO IF LABEL NIL
%token OF PACKED PROCEDURE PROGRAM RECORD REPEAT SET THEN TO TYPE UNTIL
%token VAR WHILE WITH


%%
 /*program    :  PROGRAM IDENTIFIER LPAREN IDENTIFIER RPAREN SEMICOLON statement DOT    { parseresult = makeprogn($1, $7);}*/
 
  program    :  PROGRAM IDENTIFIER LPAREN IDENTIFIER RPAREN SEMICOLON block DOT    { parseresult = processProgram($1, $2, $4, $5, $7);}
             ;
			 
	block	: cblock	
			| vblock
			| pblock
			| tblock
			| statement						
			;
			
	tblock 	: TYPE tspec block {$$ = $3;}
			;
			
	tspec   : typegroup SEMICOLON tspec 	
			| typegroup SEMICOLON	
			;
			
typegroup   : IDENTIFIER EQ type 		{insttype($1, $3);}
			;
			
	pblock  : LABEL numberlist SEMICOLON block {$$ = $4;}
			;
	
 numberlist : NUMBER COMMA numberlist 			{instlabel($1);}
			| NUMBER							{instlabel($1);}
			;
			 
	vblock	: VAR varspecs block				{$$ = $3;}
			;
			
	cblock	: CONST eqspec block {$$ = $3;}
			;
	
	eqspec 	: IDENTIFIER EQ expr SEMICOLON eqspec {instconst($1, $3);}
			| IDENTIFIER EQ expr SEMICOLON		{instconst($1, $3);}
			;
			
	varspecs: vargroup SEMICOLON varspecs
			| vargroup SEMICOLON
			;
			
	vargroup: idlist COLON type 				{instvars($1, $3);}
			;
			 
	type	: simpletype						{$$ = $1;}
			| RECORD fieldlist END				{$$ = instrec($1, $2);}
			| POINT IDENTIFIER					{$$ = instpoint($1, $2);}
			| ARRAY LBRACKET arglist RBRACKET OF type {$$ = instarray($3, $6);}
			;

	arglist : simpletype COMMA arglist			{$$ = cons($1, $3);}
			| simpletype
			;
	
fieldlist	: idlist COLON type SEMICOLON fieldlist	{$$ = nconc(instfields($1, $3), $5);}
			| idlist COLON type						{instfields($1, $3);}
			;
			
	idlist  : IDENTIFIER COMMA idlist 			{$$ = cons($1, $3);}
			| IDENTIFIER 						{$$ = cons($1, NULL);}
			;
			
	simpletype: IDENTIFIER						{$$ = findtype($1);}
			| LPAREN idlist RPAREN				{$$ = instenum($2);}
			| NUMBER DOTDOT NUMBER				{$$ = makesubrange($2, $1->intval, $3->intval);}
			;
  statement  : NUMBER COLON statement			{$$ = dolabel($1, $2, $3);}
			 | BEGINBEGIN statement endpart
			        							{ $$ = makeprogn($1,cons($2, $3)); }
             |  IF expr THEN statement endif   		{ $$ = makeif($1, $2, $4, $5); }
			 | 	FOR assignment TO expr DO statement	{ $$ = makefor(1, $1, $2, $3, $4, $5, $6);}
			 | REPEAT repeatTerms UNTIL expr		{$$ = makerepeat($1, $2, $3, $4);}
			 | exprORassign
             ;
			 
repeatTerms : exprORassign SEMICOLON repeatTerms { $$ = cons($1, $3);}
			| exprORassign
			;
			
exprORassign : expr
			 | assignment
		     ;
			 
  endpart    :  SEMICOLON statement endpart    { $$ = cons($2, $3); }
             |  END                            { $$ = NULL; }
             ;
			 
  endif      :  ELSE statement                 { $$ = $2; }
             |  /* empty */                    { $$ = NULL; }
             ;
			 
  assignment :  variable ASSIGN expr         { $$ = binop($2, $1, $3); }
             ;
			 
variable	 : variable DOT IDENTIFIER		{$$ = reducedot($1, $2, $3);}
			 | variable POINT				{$$ = dopoint($1, $2);}
			 | IDENTIFIER
			 ;
			 
  expr       :   IDENTIFIER EQ expr				{$$ = binop($2, $1, $3);}
			 | expr PLUS term                 { $$ = binop($2, $1, $3); }
			 | factor TIMES factor					{ $$ = binop($2, $1, $3);}
			 | MINUS factor						{$$ = unaryop($1, $2);}
			 | factor MINUS factor				{$$ = binop($2, $1, $3);}
			 | STRING
             |  term 
			 | factor
             ;
			 
  term       :  term TIMES factor              { $$ = binop($2, $1, $3); }
		     | term MINUS factor					{$$ = binop($2, $1, $3);}
             |  factor TIMES factor
			 |  factor
             ;
			 
  factor     :  LPAREN expr RPAREN             { $$ = $2; }
             |  IDENTIFIER LPAREN expr RPAREN { $$ = makefuncall($2, $1, $3);}
			 |  IDENTIFIER						{$$ = findid($1);/* want to replace constants with actual value here?? */}
             |  NUMBER
             ;

%%

/* You should add your own debugging flags below, and add debugging
   printouts to your programs.

   You will want to change DEBUG to turn off printouts once things
   are working.
  */

#define DEBUG        0             /* set bits here for debugging, 0 = off  */  //default 31
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */

 int labelnumber = 0;  /* sequential counter for internal label numbers */

/* dolabel is the action for a label of the form   <number>: <statement>
   tok is a (now) unused token that is recycled. */
TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement){
	printf("doing label...\n");
	TOKEN progn = makeprogn(tok, statement);
	TOKEN label = talloc();
	label->tokentype = OPERATOR;
	label->whichval = LABELOP;
	label->operands = labeltok;
	//replace number with internal lable
	int i = 0;
	while(labels[i] != labeltok->intval)
		i++;
	labeltok->intval = i;
	progn->operands = label;
	label->link = statement;
	
	return progn;
}
 
/* reducedot handles a record reference.
   dot is a (now) unused token that is recycled. */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field){
	printf("making aref..\n");
	TOKEN aref = talloc();
	if(var->whichval == AREFOP){
		printf("var is aref!!!\n");
		printf("previous field accessed: %s\n", var->symtype->namestring);
		//need to add to offset
		printf("field: %s\n", field->stringval);
		SYMBOL record = var->symtype->datatype;
		SYMBOL ff = record->datatype->datatype;										//gets me the symbol for the first field
		int offset = 0;
		while(ff && (strcmp(ff->namestring, field->stringval) != 0)){
			printf("field: %s\n", ff->namestring);
			//add padding. this could be avoided if each field in a record recorded it's own offset. I guess i haven't done this
			offset += ff->size;
			if((offset % 8 != 0) && (ff->size == 8)){
				offset += 4;
				printf("added padding\n");
			}
			printf("offset = %d\n", offset);
			ff = ff->link;
		}
		//link aref to field accessed. useful to multiple dot operatos
		aref->symtype = ff;
		
		//special case for padding at end
		if((offset % 8 != 0) && (ff->size == 8)){
				offset += 4;
				printf("added padding\n");
		}
		
		//adding offset to previous aref offset. Doing this because redundant aref was removed
		var->operands->link->intval += offset;
		
		return var;
	}
	else{	
		aref->tokentype = OPERATOR;
		aref->whichval = AREFOP;
		aref->operands = var;
		//link var to its offset in the record
		printf("symbol name: %s\n", var->symtype->namestring);
		//printf("%d\n", var->symtype->datatype->datatype->datatype->size);
		SYMBOL record = var->symtype->datatype->datatype->datatype;
		SYMBOL ff = record->datatype->datatype;										//gets me the symbol for the first field
		int offset = 0;
		//printing out field names
		while(ff && (strcmp(ff->namestring, field->stringval) != 0)){
			printf("field: %s\n", ff->namestring);
			//add padding. this could be avoided if each field in a record recorded it's own offset. I guess i haven't done this
			offset += ff->size;
			if((offset % 8 != 0) && (ff->size == 8)){
				offset += 4;
				printf("added padding\n");
			}
			printf("offset = %d\n", offset);
			ff = ff->link;
		}
		//link aref to field accessed. useful to multiple dot operatos
		aref->symtype = ff;
		
		//special case for padding at end
		if((offset % 8 != 0) && (ff->size == 8)){
				offset += 4;
				printf("added padding\n");
			}
			
		printf("field: %s\n", ff->namestring);
		
		printf("aref offset = %d\n\n", offset);
		//create number token for offset
		TOKEN number = talloc();
		number->tokentype = NUMBERTOK;
		number->datatype = INTEGER;
		number->intval = offset;
		var->link = number;
	}
	

	
	
	return aref;
}
 
 /* dopoint handles a ^ operator.
   tok is a (now) unused token that is recycled. */
TOKEN dopoint(TOKEN var, TOKEN tok){
	//printf("handling point...\n");
	TOKEN pointer = talloc();
	pointer->tokentype = OPERATOR;
	pointer->whichval = POINTEROP;
	pointer->operands = var;
	SYMBOL id = searchst(var->stringval);
	//printf("%s\n", id->namestring);
	pointer->symtype = id;						//linking pointer to id's symbol in table
	return pointer;
}
 
 /* instarray installs an array declaration into the symbol table.
   bounds points to a SUBRANGE symbol table entry.
   The symbol table pointer is returned in token typetok. */
TOKEN instarray(TOKEN bounds, TOKEN typetok){
	

	//printf("installing array with bounds %d .. %d\n", bounds->symtype->lowbound, bounds->symtype->highbound);
	//need to point typetok to the symbol for the type of array
	SYMBOL array = makesym("array");
	array->kind = ARRAYSYM;
	array->datatype = typetok->symtype;
	array->highbound = bounds->symtype->highbound;
	array->lowbound = bounds->symtype->lowbound;
	int size = array->datatype->size * (array->highbound - array->lowbound + 1);
	//printf("array size = %d\n", size);
	array->size = size;

	//this works for only 2 dimensional arrays right now. DO inner arrays first!!!
	TOKEN second_array;
	if(bounds->link){
		//create another array for the next dimension
		printf("creating second array\n");
		//printf("second bounds are %d .. %d\n", bounds->link->symtype->datatype->lowbound, bounds->link->symtype->datatype->highbound);
		//these are the correct bounds
		int high = bounds->link->symtype->datatype->highbound;
		int low = bounds->link->symtype->datatype->lowbound;
		//printf("new high: %d, new low: %d\n", high, low);
		TOKEN subrange = makesubrange(copytoken(typetok), low, high);
		second_array = instarray(subrange, typetok);
		array->datatype = second_array->symtype;
		//update size
		array->size = array->datatype->size * (array->highbound - array->lowbound + 1);
	}
	
	
	
	

	typetok->symtype = array;
	return typetok;
}
 
 /* instpoint will install a pointer type in symbol table */
TOKEN instpoint(TOKEN tok, TOKEN typename){
	//printf("installing pointer...\n");
	SYMBOL tsym = searchst(typename->stringval);
	//printf("%s\n", typename->stringval);
	SYMBOL temp = insertsym(typename->stringval);
	temp->kind = TYPESYM;
	
	
	SYMBOL pointersym = makesym(typename->stringval);		
	pointersym->kind = POINTERSYM;
	pointersym->datatype = temp;
	pointersym->size = basicsizes[POINTER];
	pointersym->basicdt = POINTER;
	//printf("POINTER = %d\n", POINTER);
	
	tok->symtype = pointersym;
	
	
	//printf("%d\n", tok->symtype->size);
	return tok;
}
 
 /* instenum installs an enumerated subrange in the symbol table,
   e.g., type color = (red, white, blue)
   by calling makesubrange and returning the token it returns. */
TOKEN instenum(TOKEN idlist){
	//printf("installing enum into symbol table...\n");
	int low = 0, high = 0;
	TOKEN temp = idlist;
	while(temp){
		temp = temp->link;
		high++;
	}
	TOKEN subrange = makesubrange(copytoken(idlist), low, high - 1);
	int i = 0;
	temp = idlist;
	TOKEN number = copytoken(idlist);
	number->tokentype = NUMBERTOK;
	number->datatype = INTEGER;
	//install constant for each value of subrange
	for(; i < high; i++){
		number->intval = i;
		instconst(temp, number);
		number = copytoken(number);
		temp = temp->link;
	}
	return subrange;
}

/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high){
	//printf("making subrange from %d to %d...\n", low, high);
	//put the pointer to the subrange symbol in tok
	SYMBOL subrange = makesym("subrange");
	subrange->kind = SUBRANGE;
	subrange->highbound = high;
	subrange->lowbound = low;
	subrange->basicdt = INTEGER;
	subrange->size = basicsizes[INTEGER];
	tok->symtype = subrange;
}
 
 /* instrec will install a record definition.  Each token in the linked list
   argstok has a pointer to its type.*/
TOKEN instrec(TOKEN rectok, TOKEN argstok){
	printf("installing record into symbol table...\n");
	SYMBOL temptab[50];
	TOKEN temp = argstok;
	while(temp){
		printf("%s: %s, ", temp->stringval, temp->symtype->namestring);
		temp = temp->link;
	}
	printf("\n");
	SYMBOL temptable[50];								//hold the symbols temporarily
	SYMBOL record = makesym("");
	record->kind = RECORDSYM;
	int size = 0;
	SYMBOL sym, typesym; int align;
	//accumulate size of each field and store in recordsym
	temp = argstok;
	SYMBOL first;
	typesym = temp->symtype;
	align = alignsize(typesym);
	int index = 0;
	while(temp){
		sym = makesym(temp->stringval);
		if(index == 0)
			first = sym;
		sym->datatype = temp->symtype;
		sym->offset += size;
		sym->size = temp->symtype->size;
		//add padding
		if((size % 8 != 0) && (temp->symtype->size == 8)){
			size += 4;
		}		
		size += temp->symtype->size;
		temptab[index] = sym;						//insert so you can link together later
		temp = temp->link;
		printf("NAME: %s, DATATYPE: %s, OFFSET: %d, SIZE: %d\n", sym->namestring, sym->datatype->namestring, sym->offset, sym->size);
		index++;
	}
	
	int i = 0;
	for(; i < index - 1; i++){
		temptab[i]->link = temptab[i+1];
	}
	

	
	record->datatype = first;
	record->size = size;
	
	printf("KIND: %d, DATATYPE: %s, SIZE: %d\n", record->kind, record->datatype->namestring, record->size);
	printf("first = %s\n", record->datatype->namestring);
	
	
	
	
	rectok->symtype = record;			//ie. "complex" datatype will point to this RECORDSYM
	printf("first = %s\n", rectok->symtype->datatype->namestring);
	printf("\n");
	return rectok;
}

/* instfields will install type in a list idlist of field name tokens:
   re, im: real    put the pointer to REAL in the RE, IM tokens.
   typetok is a token whose symtype is a symbol table pointer.
   Note that nconc() can be used to combine these lists after instrec() */
TOKEN instfields(TOKEN idlist, TOKEN typetok){
	//printf("inside instfields...\n");
	TOKEN temp = idlist;
	while(temp){
		temp->symtype = typetok->symtype;			//connecting each id in list to it's type
		//printf("%s, ", temp->stringval);
		temp = temp->link;
	}

	
	//printf("\n%s\n", typetok->symtype->namestring);
	
	//printf("\n"); 
	return idlist;
}
 
 /* insttype will install a type name in symbol table.
   typetok is a token containing symbol table pointers. */
void  insttype(TOKEN typename, TOKEN typetok){
	printf("installing %s into symbol table...\n", typename->stringval);
	printf("previous entry for %s...?", typename->stringval);
	//printf("size: %d\n", typetok->symtype->datatype->size);
	SYMBOL temp = searchst(typename->stringval);
	if(temp){
		printf(" yes!\n");
		temp->kind = TYPESYM;
		temp->datatype = typetok->symtype;
		temp->size = typetok->symtype->size;
		temp->basicdt = typetok->symtype->basicdt;
	}
	else{
		printf(" no\n");
	
	//make a symbol for typename. Datatype for sym = typetok->symtype
	SYMBOL typesym = insertsym(typename->stringval);
	typesym->kind = TYPESYM;
	typesym->datatype = typetok->symtype;
	typesym->size = typetok->symtype->size;
	typesym->basicdt = typetok->symtype->basicdt;
	
	}
	//printf("%s\n", typetok->symtype->datatype->namestring);

	printf("\n\n");
	
	
	


}
 
 /* instlabel installs a user label into the label table */
void  instlabel (TOKEN num){
	printf("installing label...\n");
	//install into label table. Index into table is the internal label
	labels[labelnumber++] = num->intval;
	int i = 0;
	for(; i < labelnumber; i++){
		printf("%d\n", labels[i]);
	}
}

/* findtype looks up a type name in the symbol table, puts the pointer
   to its type into tok->symtype, returns tok. */
TOKEN findtype(TOKEN tok){
	printf("linking %s to it's type...\n", tok->stringval);
	SYMBOL stype = searchst(tok->stringval);
	tok->symtype = stype;
	//if stype is null then the type isn't a basic type or it hasn't been entered into symbol table yet
	printf("%s\n", tok->symtype->namestring);
	printf("high: %d, low: %d\n", stype->highbound, stype->lowbound);
	return tok;
}
 
 /* findid finds an identifier in the symbol table, sets up symbol table
   pointers, changes a constant to its number equivalent */
TOKEN findid(TOKEN tok){
	SYMBOL result = searchst(tok->stringval);
	TOKEN constant_val = copytoken(tok);
	//if id is in symbol table and 
	if((result != NULL) && (result->kind == CONSTSYM)){
		//printf("found constant variable in symbol table. need to replace with actual value\n\n");
		//printf("token name = %s\n", tok->stringval);
		constant_val->tokentype = NUMBERTOK;
		constant_val->datatype = result->basicdt;			//copy datatype
		//printf("datatype = %d\n", result->basicdt); 
		//integer
		if(constant_val->datatype == 0){
			constant_val->intval = result->constval.intnum;
			//printf("constant_value = %d\n\n", constant_val->intval);
		}
		//real
		else if(constant_val->datatype == 1){
			constant_val->realval = result->constval.realnum;
			//printf("constant_value = %f\n\n", constant_val->realval);
		}
		return constant_val;
	}
	return tok;
	

}
 
 /* makerepeat makes structures for a repeat statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr){
	TOKEN copy_tok = copytoken(tok);
	//creating label operator token
	convert(tokb, LABELOP);			//make a new number for the label. use unaryop??
	makeprogn(copy_tok, tokb);
	//creating number for label
	TOKEN new = talloc();			//use this for number of label??
	new->tokentype = NUMBERTOK;
	new->datatype = INTEGER;
	new->intval = labelnumber++;
	//connecting label to its number
	unaryop(tokb, new);
	
	//linking label to statements
	tokb->link = statements;
	
	TOKEN if_copy = copytoken(tokb);
	if_copy->whichval = IFOP;
	if_copy->operands = expr;
	if_copy->link = NULL;
	TOKEN link_pointer = statements->link;
	while(link_pointer->link != NULL)
		link_pointer = link_pointer->link;
	link_pointer->link = if_copy;
	
	//attach progn to expr
	expr->link = makeprogn(copytoken(tok), NULL);
	
	//create goto
	TOKEN gotok = copytoken(if_copy);
	gotok->whichval = GOTOOP;
	gotok->link = NULL;
	TOKEN label_num = copytoken(new);
	//label_num->intval = new->intval;
	label_num->link = NULL;
	label_num->operands = NULL;
	gotok->operands = label_num;
	
	//connect progn to goto
	expr->link->link = gotok;
	
	return copy_tok;
}
 
/* instconst installs a constant in the symbol table */
void  instconst(TOKEN idtok, TOKEN consttok){
	SYMBOL sym, typesym; int align;
	//typesym = consttok->symtype;				//this doesnt work but was provided in class notes. 
	if(consttok->datatype == 1){
		typesym = searchst("real");		//this works though...
	}
	else if(consttok->datatype == 0){
		typesym = searchst("integer");
	}
	//printsymbol(typesym);
	align = alignsize(typesym);
	printf("align = %d\n", align);
	
	sym = insertsym(idtok->stringval);
	sym->kind = CONSTSYM;
	//sym->offset = wordaddress(blockoffs[blocknumber], align);
	sym->size = typesym->size;
	//blockoffs[blocknumber] = sym->offset + sym->size;
	sym->datatype = typesym;
	sym->basicdt = typesym->basicdt;
	if(consttok->datatype == 0)
		sym->constval.intnum = consttok->intval;
	else if(consttok->datatype == 1)
		sym->constval.realnum = consttok->realval;
}
 
   /*  Note: you should add to the above values and insert debugging
       printouts in your routines similar to those that are shown here.     */
	   
//processes first part of program
TOKEN processProgram(TOKEN tok1, TOKEN tok2, TOKEN tok3, TOKEN tok4, TOKEN tok5){
	convert(tok1, PROGRAMOP);		//fix this garbage
	link(tok1, tok2);
	tok2->link = makeprogn(tok4, tok3);
	tok4->link = tok5;
	tok3->operands = tok5;
	parseresult = tok1;
	return tok1;
}

/* instvars will install variables in symbol table.
   typetok is a token containing symbol table pointer for type. */
void  instvars(TOKEN idlist, TOKEN typetok){

	//need to link typetok to its symbol in table
	

	printf("\ninstalling vars...\n");
	SYMBOL sym, typesym; int align;
	typesym = typetok->symtype;				//original
	//typesym = searchst(typetok->stringval);		//my temp fix. Dont believe I need this anymore. Working correctly now.
	printf("type name is %s\n", typetok->stringval);
	printf("basicdt = %d\n", typetok->datatype);
	printf("typesym basicdt = %d\n", typesym->basicdt);
	printf("symtype = %s\n", typetok->symtype->namestring);
	if(typesym->datatype)
		printf("symtype size = %d\n\n", typesym->datatype->datatype->size);
	align = alignsize(typesym);
	//for each id
	while(idlist != NULL){ 		
		sym = insertsym(idlist->stringval);
		sym->kind = VARSYM;
		sym->offset = wordaddress(blockoffs[blocknumber], align);
		sym->size = typesym->size;
		blockoffs[blocknumber] = sym->offset + sym->size;
		sym->datatype = typesym;
		sym->basicdt = typesym->basicdt;
		idlist = idlist->link;
	}
}
	   
//returns a copy of the token
TOKEN copytoken(TOKEN tok){
	TOKEN new = talloc();
	new->tokentype = tok->tokentype;
	new->datatype = tok->datatype;
	new->symtype = tok->symtype;
	new->symentry = tok->symentry;
	new->operands = tok->operands;
	new->link = tok->link;
	new->realval = tok->realval;
	return new;
}

/* makefuncall makes a FUNCALL operator and links it to the fn and args.
   tok is a (now) unused token that is recycled. */
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args)
{
	TOKEN func;
	func = copytoken(tok);
	func->tokentype = OPERATOR;
	func->datatype = STRINGTYPE;
	func->whichval = FUNCALLOP;
	func->link = NULL;
	
	if(strcmp(fn->stringval, "new") == 0){
		printf("making new function...\n");
		//create number token for size of allocated memory
		TOKEN size = copytoken(tok);
		size->tokentype = NUMBERTOK;
		size->datatype = INTEGER;
		size->symtype = searchst("integer");
		size->operands = NULL;
		size->link = NULL;
		size->intval = searchst(args->stringval)->datatype->datatype->datatype->size;
		printf("%s\n", args->stringval);
		printf("%d\n", searchst(args->stringval)->datatype->datatype->datatype->size);		//first dt points to pp, next points to person pointer, next points to person??
		fn->link = size;
		func->operands = fn;
		//create an assignop. operand is fn...
		TOKEN assignop = copytoken(size);
		assignop->whichval = ASSIGNOP;
		assignop->tokentype = OPERATOR;
		
		return binop(assignop, args, func);
		
	}
	
	else{
		fn->link = args;
		func->operands = fn;
		
		//search symbol table for function. Need to check if arguments need to be coerced
		SYMBOL func_symbol = searchst(fn->stringval);
		int return_type = func_symbol->datatype->basicdt;
		int arg_type = func_symbol->datatype->link->basicdt;
		printf("\n\nfunction name is %s\n", fn->stringval);
		printf("function return type = %d\n", return_type);
		printf("function argument type = %d\n\n", arg_type);
	}

	return func;
}

/* makefor makes structures for a for statement.
   sign is 1 for normal loop, -1 for downto.
   asg is an assignment statement, e.g. (:= i 1)
   endexpr is the end expression
   tok, tokb and tokc are (now) unused tokens that are recycled. */
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr,
              TOKEN tokc, TOKEN statement)
{
	//creating label operator token
	convert(tokb, LABELOP);			//make a new number for the label. use unaryop??
	makeprogn(tok, asg);
	cons(asg, tokb);
	//creating number for label
	TOKEN new = talloc();			//use this for number of label??
	new->tokentype = NUMBERTOK;
	new->datatype = INTEGER;
	new->intval = labelnumber++;
	//connecting label to its number
	unaryop(tokb, new);
	//creating ifop
	TOKEN ifop = talloc();
	ifop->tokentype = OPERATOR;
	ifop->datatype = STRINGTYPE;
	ifop->whichval = IFOP;
	cons(tokb, ifop);
	//creating assignment statement
	TOKEN lteop = talloc();
	lteop->tokentype = OPERATOR;
	lteop->datatype = STRINGTYPE;
	lteop->whichval = LEOP;
	unaryop(ifop, lteop);
	//add operands to LEOP
	TOKEN i = copytoken(asg->operands);
	
	binop(lteop, i, endexpr);
	//connect progn to LEOP
	TOKEN newProgn = makeprogn(copytoken(i), statement);
	newProgn->link = NULL;				//null link left over from copying
	cons(lteop, newProgn);
	
	//part for incrementing loop variable
	TOKEN assignop = copytoken(ifop);
	assignop->whichval = ASSIGNOP;
	//create second operand of incrementation
	TOKEN plusop = copytoken(assignop);
	plusop->whichval = PLUSOP;
	plusop->link = NULL;
	TOKEN one = copytoken(new);
	one->intval = 1;
	binop(plusop, copytoken(i), one);
	binop(assignop, copytoken(i), plusop);
	
	statement->link = assignop;
	/* TOKEN pointer = statement->link->operands;
	//skip progn and attach incrementation to end of arguments
	while(pointer->link != NULL)
		pointer = pointer->link;
	pointer->link = assignop; */
	
	
	//create goto
	TOKEN gotok = copytoken(plusop);
	gotok->whichval = GOTOOP;
	gotok->link = NULL;
	TOKEN zero = copytoken(one);
	zero->intval = labelnumber-1;
	zero->link = NULL;
	zero->operands = NULL;
	gotok->operands = zero;
	cons(assignop, gotok);
	
	return tok;
}

/*link tok with other*/
TOKEN link(TOKEN tok, TOKEN other){
	tok->tokentype = OPERATOR;
	tok->link = other;
	tok->operands = other;
	return tok;
}	

/*converts one token to another type*/
TOKEN convert(TOKEN tok, int opnum){
	tok->tokentype = OPERATOR;
	tok->whichval = opnum;
	return tok;
}

/* nconc concatenates two token lists, destructively, by making the last link
   of lista point to listb.
   (nconc '(a b) '(c d e))  =  (a b c d e)  */
/* nconc is useful for putting together two fieldlist groups to
   make them into a single list in a record declaration. */
TOKEN nconc(TOKEN lista, TOKEN listb){
	TOKEN temp = lista;
	while(temp->link)
		temp = temp->link;
	temp->link = listb;
	return lista;
	
}
	   
TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
  { item->link = list;
    if (DEBUG & DB_CONS)
       { printf("cons\n");
         dbugprinttok(item);
         dbugprinttok(list);
       };
    return item;
  }

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)        /* reduce binary operator */
  { op->operands = lhs;          /* link operands to operator       */
    lhs->link = rhs;             /* link second operand to first    */
    rhs->link = NULL;            /* terminate operand list          */
	TOKEN op_copy = copytoken(op);
	//getting type of second argument
	SYMBOL second = searchst(rhs->stringval);
	if(second != NULL)
		printf("rhs datatype = %d\n\n", second->basicdt);
	
	//need to coerce integer to float.
	if((second != NULL) && (lhs->datatype != second->basicdt) && (rhs->datatype != STRINGTYPE) && (lhs->whichval != 25)){		//hardcoded special case for arefop. Should not do this!!!
		//coerce lhs to float
		if(lhs->datatype == INTEGER){
			printf("coercing...\n");
			printf("lhs %d\n", lhs->whichval);
			op_copy->whichval = FLOATOP;
			op_copy->operands = lhs;
			lhs->link = NULL;
			op_copy->link = rhs;
			op->operands = op_copy;
			
		}
		//coerce rhs to float
		else if(rhs->datatype == INTEGER){
			op_copy->whichval = FLOATOP;
			op_copy->operands = rhs;
			op_copy->link = NULL;
			lhs->link = op_copy;
		}
	}
	//lhs is an aref
	if(lhs->whichval == 25){
		printf("\ninside binop...\n");
		printf("%s\n", lhs->symtype->datatype->namestring);
		SYMBOL type = searchst(lhs->symtype->datatype->namestring);
		//printf("%d\n", type->datatype->size);
	}
	
    if (DEBUG & DB_BINOP)
       { printf("binop\n");
         dbugprinttok(op);
         dbugprinttok(lhs);
         dbugprinttok(rhs);
       };
    return op;
  }
  
/* unaryop links a unary operator op to one operand, lhs */
TOKEN unaryop(TOKEN op, TOKEN lhs){
	op->operands = lhs;
	lhs->link = NULL;
	return op;
}

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
  {  tok->tokentype = OPERATOR;  /* Make it look like an operator   */
     tok->whichval = IFOP;
     if (elsepart != NULL) elsepart->link = NULL;
     thenpart->link = elsepart;
     exp->link = thenpart;
     tok->operands = exp;
     if (DEBUG & DB_MAKEIF)
        { printf("makeif\n");
          dbugprinttok(tok);
          dbugprinttok(exp);
          dbugprinttok(thenpart);
          dbugprinttok(elsepart);
        };
     return tok;
   }

   /* makeprogn makes a PROGN operator and links it to the list of statements.
   tok is a (now) unused token that is recycled. */
TOKEN makeprogn(TOKEN tok, TOKEN statements)
  {  tok->tokentype = OPERATOR;
     tok->whichval = PROGNOP;
     tok->operands = statements;
     if (DEBUG & DB_MAKEPROGN)
       { printf("makeprogn\n");
         dbugprinttok(tok);
         dbugprinttok(statements);
       };
     return tok;
   }

int wordaddress(int n, int wordsize)
  { return ((n + wordsize - 1) / wordsize) * wordsize; }
 
yyerror(s)
  char * s;
  { 
  fputs(s,stderr); putc('\n',stderr);
  }

main()
  { int res;
    initsyms();
    res = yyparse();
    printst();
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);           /* Pretty-print the result tree */
  }
